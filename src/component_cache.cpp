/*
 * component_cache.cpp
 *
 *  Created on: Feb 5, 2013
 *      Author: mthurley
 */

#include "component_cache.h"

#include <algorithm>

#ifdef __linux__

#include <sys/sysinfo.h>
#include <cstdint>

uint64_t freeram() {

  struct sysinfo info;
      sysinfo(&info);

  return info.freeram *(uint64_t) info.mem_unit;
}

#elif __APPLE__ && __MACH__

#include <sys/types.h>
#include <sys/sysctl.h>


uint64_t freeram() {

  int mib[2];
  int64_t physical_memory;
  mib[0] = CTL_HW;
  mib[1] = HW_MEMSIZE;
  size_t length = sizeof(int64_t);
  sysctl(mib, 2, &physical_memory, &length, NULL, 0);

  return physical_memory;
}

#else

#endif



#include "stack.h"


ComponentCache::ComponentCache(SolverConfiguration &config, DataAndStatistics &statistics) :
		config_(config), statistics_(statistics) {
//   cout << sizeof(CacheableComponent) << " " << sizeof(mpz_class) << endl;
  my_time_ = 1;

  entry_base_.clear();
  entry_base_.reserve(2000000);
  entry_base_.push_back(new CacheableComponent()); // dummy Element
  table_.clear();
  table_.resize(1024*1024, 0);
  table_size_mask_ = table_.size() - 1;

  free_entry_base_slots_.clear();
  free_entry_base_slots_.reserve(10000);

  compute_byte_size_infrasture();

  uint64_t free_ram = freeram();
  uint64_t max_cache_bound = 95 * (free_ram / 100);

  if (config_.maximum_cache_size_bytes_ == 0) {
    config_.maximum_cache_size_bytes_ = max_cache_bound;
  }

  if(!config_.quiet){
    if (config_.maximum_cache_size_bytes_ > free_ram) {
      cout << endl <<" WARNING: Maximum cache size larger than free RAM available" << endl;
      cout << " Free RAM " << free_ram / 1000000 << "MB" << endl;
    }

    cout << "Maximum cache size:\t"
        << config_.maximum_cache_size_bytes_ / 1000000 << " MB" << endl
        << endl;
  }

  assert(!cache_full());

  //TODO this should be pointless, remove unless problems occur
//   if (entry_base_.capacity() == entry_base_.size())
//     entry_base_.reserve(2 * entry_base_.size());

  // dummy element as super component, must be replaced before solving
  CacheableComponent& packed_super_comp = *new CacheableComponent();
  entry_base_.push_back(&packed_super_comp);
  statistics_.incorporate_cache_store(packed_super_comp);
}

void ComponentCache::clear(){
  // clears the entry base
  for(unsigned int i = 2; i < entry_base_.size(); i++){
    if(entry_base_[i]){
      statistics_.incorporate_cache_erase(*entry_base_[i]);
      delete entry_base_[i];
      entry_base_[i] = nullptr;
    }
  }
  // the first two elements are dummys
  entry_base_.resize(2);

  free_entry_base_slots_.clear();

  // clears the hash table
  unsigned int current_table_size =  table_.size();
  table_.clear();
  table_.resize(current_table_size, 0);

  // removes invalid references from super component
  entry(1).set_first_descendant(0);
  entry(1).set_next_sibling(0);
  entry(1).set_next_bucket_element(0);
}


void ComponentCache::adjustPackSize(unsigned int maxVarId, unsigned int maxClId){
  if(!BasePackedComponent::testPackSizeAdjustment(maxVarId, maxClId)){
    // we can skip the rest if nothing would change
    return;
  }

  // changing the packsize can change the size of the entries, so we need to redo the statistics
  for(CacheableComponent* current_entry: entry_base_){
    if(current_entry){
      statistics_.incorporate_cache_erase(*current_entry);
    }
  }

  BasePackedComponent::adjustPackSize(maxVarId, maxClId);

  for(CacheableComponent* current_entry: entry_base_){
    if(current_entry){
      // unpacks with the old sizes, repacks with the new ones
      Component unpacked = current_entry->unpack(true);
      current_entry->pack(unpacked);

      statistics_.incorporate_cache_store(*current_entry);
    }
  }
}

void ComponentCache::setSuperComponent(Component& super_comp){
    CacheableComponent &packed_super_comp = *new CacheableComponent(super_comp);

    // transfering the relevant structural data from the old super component
    packed_super_comp.set_first_descendant(entry(1).first_descendant());

    // deleting the old super component
    statistics_.incorporate_cache_erase(entry(1));
    delete entry_base_[1];

    statistics_.incorporate_cache_store(packed_super_comp);
    entry_base_[1] = &packed_super_comp;
    super_comp.set_id(1);
}

void ComponentCache::translate(vector<unsigned int>& translation_table){
  for(unsigned int id = 2; id < entry_base_.size(); id++){
    CacheableComponent* entry = entry_base_[id];
    if(entry != nullptr){
      Component unpacked = entry->unpack();
      if(!unpacked.empty()){
        bool erased = false;
        for(auto clause = unpacked.clsBegin(); *clause != clsSENTINEL; clause++){
          // if a clause has been removed, the entry will never occur again
          if(translation_table[*clause] == NOT_A_CLAUSE){
            removeFromHashTable(id);
            removeFromDescendantsTree(id);
            eraseEntry(id);
            erased = true;
            break;
          // otherwise, we translate
          } else{
            *clause = translation_table[*clause];
          }
        }

        if(!erased){
          // entry might change size due to the renaming
          statistics_.incorporate_cache_erase(*entry);

          //repack the changed component
          entry->pack(unpacked);

          // entry might have changed size due to the renaming
          statistics_.incorporate_cache_store(*entry);
        }
      }
    }
  }
}

void ComponentCache::remove_damaged_entries(vector<LiteralID>::iterator damaging_clause){
  // we will traverse the tree formed by the entries, because we do not need to consider the children if we did not need to delete the parent
  vector<CacheEntryID> stack;

  // we skip the root, because we cannot delete it. Instead, we add all its children to the stack
  for(CacheEntryID current_child = entry(1).first_descendant(); current_child && hasEntry(current_child); current_child = entry(current_child).next_sibling()){
    stack.push_back(current_child);
  }

  // for every entry on the stack, we check if it is still valid
  while(!stack.empty()){
    // depth-first traversal
    CacheEntryID current_id = stack.back();
    stack.pop_back();

    if(current_id && hasEntry(current_id)){
      Component unpacked = entry(current_id).unpack();

      // damaging_clause invalidates the entry if all its variables are contained within, because then it would be implicitly included
      bool completely_contained = true;
      for(auto it =  damaging_clause; *it != SENTINEL_LIT; it++){
        // the variables should be sorted in the component
        if(!binary_search(unpacked.varsBegin(), unpacked.varsBegin() + unpacked.num_variables(), it -> var())){
          completely_contained = false;
          break;
        }
      }
      if(completely_contained){
        // the children might need to be deleted as well
        for(CacheEntryID current_child = entry(current_id).first_descendant(); current_child && hasEntry(current_child); current_child = entry(current_child).next_sibling()){
          stack.push_back(current_child);
        }

        // delete the entry
        removeFromDescendantsTree(current_id);
        eraseEntry(current_id);
      }
    }
  }
}


void ComponentCache::test_descendantstree_consistency() {
	for (unsigned id = 2; id < entry_base_.size(); id++)
		if (entry_base_[id] != nullptr) {
			CacheEntryID act_child = entry(id).first_descendant();
			while (act_child) {
				CacheEntryID next_child = entry(act_child).next_sibling();
				assert(entry(act_child).father() == id);

				act_child = next_child;
			}
			CacheEntryID father = entry(id).father();
			CacheEntryID act_sib = entry(father).first_descendant();

			bool found = false;

			while (act_sib) {
				CacheEntryID next_sib = entry(act_sib).next_sibling();
				if (act_sib == id)
					found = true;
				act_sib = next_sib;
			}
			assert(found);
		}
}


bool ComponentCache::deleteEntries() {
    assert(cache_full());

	vector<double> scores;
	for (auto it = entry_base_.begin() + 1; it != entry_base_.end(); it++)
		if (*it != nullptr && (*it)->isDeletable()) {
			scores.push_back((double) (*it)->creation_time());
		}

    if(scores.size() == 0){
      // nothing can be deleted
      //TODO this might be the point to return false. Unfortunately, the solver neither documents nor uses the return value
      return true;
    }

	sort(scores.begin(), scores.end());
	double cutoff = scores[scores.size() / 2];

	//cout << "cutoff" << cutoff  << " entries: "<< entry_base_.size()<< endl;

	// first : go through the EntryBase and mark the entries to be deleted as deleted (i.e. EMPTY
	// note we start at index 2,
	// since index 1 is the whole formula,
	// should always stay here!
	for (unsigned id = 2; id < entry_base_.size(); id++)
		if (entry_base_[id] != nullptr &&
		    entry_base_[id]->isDeletable() &&
            (double) entry_base_[id]->creation_time() <= cutoff) {
				removeFromDescendantsTree(id);
				eraseEntry(id);
        }
	// then go through the Hash Table and erase all Links to empty entries

#ifdef DEBUG
	test_descendantstree_consistency();
#endif

	reHashTable(table_.size());
	statistics_.sum_size_cached_components_ = 0;
	statistics_.sum_bytes_cached_components_ = 0;
	 statistics_.sys_overhead_sum_bytes_cached_components_ =0;

	statistics_.sum_bytes_pure_cached_component_data_ = 0;

	for (unsigned id = 2; id < entry_base_.size(); id++)
		if (entry_base_[id] != nullptr) {
			statistics_.sum_size_cached_components_ +=
					entry_base_[id]->num_variables();
			statistics_.sum_bytes_cached_components_ +=
			    entry_base_[id]->SizeInBytes();
			statistics_.sum_bytes_pure_cached_component_data_ +=
			    entry_base_[id]->data_only_byte_size();
			 statistics_.sys_overhead_sum_bytes_cached_components_ +=
			     entry_base_[id]->sys_overhead_SizeInBytes();
		}

	statistics_.num_cached_components_ = entry_base_.size();
	compute_byte_size_infrasture();

	//cout << " \t entries: "<< entry_base_.size() - free_entry_base_slots_.size()<< endl;
	return true;
}


uint64_t ComponentCache::compute_byte_size_infrasture() {
  statistics_.cache_infrastructure_bytes_memory_usage_ =
      sizeof(ComponentCache)
      + sizeof(CacheEntryID)* table_.capacity()
      + sizeof(CacheableComponent *)* entry_base_.capacity()
      + sizeof(CacheEntryID) * free_entry_base_slots_.capacity();
  return statistics_.cache_infrastructure_bytes_memory_usage_;
}

void ComponentCache::debug_dump_data(){
    cout << "sizeof (CacheableComponent *, CacheEntryID) "
         << sizeof(CacheableComponent *) << ", "
         << sizeof(CacheEntryID) << endl;
    cout << "table (size/capacity) " << table_.size()
         << "/" << table_.capacity() << endl;
    cout << "entry_base_ (size/capacity) " << entry_base_.size()
             << "/" << entry_base_.capacity() << endl;
    cout << "free_entry_base_slots_ (size/capacity) " << free_entry_base_slots_.size()
             << "/" << free_entry_base_slots_.capacity() << endl;

//    uint64_t size_model_counts = 0;
    uint64_t alloc_model_counts = 0;
    for (auto &pentry : entry_base_)
              if (pentry != nullptr){
//                size_model_counts += pentry->size_of_model_count();
                alloc_model_counts += pentry->alloc_of_model_count();
              }
    cout << "model counts size " << alloc_model_counts << endl;
}





