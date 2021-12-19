/*
 * component_management.cpp
 *
 *  Created on: Aug 23, 2012
 *      Author: Marc Thurley
 */

#include "component_management.h"


void ComponentManager::prepare(LiteralIndexedVector<Literal>& literals, vector<LiteralID>& lit_pool,
                               vector<ClauseOfs>& added_long_clauses_, vector<BinaryClause>& added_binary_clauses_,
                               vector<LiteralID>& added_unit_clauses_, vector<LiteralID> &assumptions_,
                               vector<vector<LiteralID>>& removed_long_clauses_, vector<BinaryClause>& removed_binary_clauses_){
  ana_.initialize(literals, lit_pool);
  // BEGIN CACHE INIT

  cache_.adjustPackSize(ana_.max_variable_id(), ana_.max_clause_id());
  removeCacheEntriesDamagedByChanges(lit_pool, added_long_clauses_, added_binary_clauses_, added_unit_clauses_, assumptions_, removed_long_clauses_, removed_binary_clauses_);

  for(Component *comp: component_stack_){
    delete comp;
  }
  component_stack_.clear();
  component_stack_.reserve(ana_.max_variable_id() + 2);
  component_stack_.push_back(new Component());
  component_stack_.push_back(new Component());
  assert(component_stack_.size() == 2);
  component_stack_.back()->createAsDummyComponent(ana_.max_variable_id(),
      ana_.max_clause_id());

  cache_.setSuperComponent(*component_stack_.back());
  // we have made enough changes to the entries that the hash table might no longer be valid
  cache_.reHashTable();
}

void ComponentManager::removeCacheEntriesDamagedByChanges(vector<LiteralID>& lit_pool,
                                                          vector<ClauseOfs>& added_long_clauses_,
                                                          vector<BinaryClause>& added_binary_clauses_,
                                                          vector<LiteralID>& added_unit_clauses_,
                                                          vector<LiteralID>& assumptions_,
                                                          vector<vector<LiteralID>>& removed_long_clauses_,
                                                          vector<BinaryClause>& removed_binary_clauses_){
  // we start with the unit clauses because they are faster and might already shrink the cache
  // removal is not necessiary, but safe as long as clauses are not removeable
  vector<LiteralID> small_clause_pool(3, SENTINEL_LIT);
  if(config_.cache_cleanup_agressiveness >= 1){
    for(LiteralID clause: added_unit_clauses_){
      small_clause_pool[0] = clause;

      cache_.remove_damaged_entries(small_clause_pool.begin());
    }
  }

  // assumptions are effectively unit clauses, but only temporary, so deletion is more ambivalent
  if(config_.cache_cleanup_agressiveness >= 2){
    for(LiteralID clause: assumptions_){
      small_clause_pool[0] = clause;

      cache_.remove_damaged_entries(small_clause_pool.begin());
    }
  }

  // continuing with the next larger clause type: binary clauses
  for(BinaryClause clause: added_binary_clauses_){
    small_clause_pool[0] = clause.first;
    small_clause_pool[1] = clause.second;

    cache_.remove_damaged_entries(small_clause_pool.begin());
  }
  for(BinaryClause clause: removed_binary_clauses_){
    small_clause_pool[0] = clause.first;
    small_clause_pool[1] = clause.second;

    cache_.remove_damaged_entries(small_clause_pool.begin());
  }

  // now the long clauses
  for(ClauseOfs clause:  added_long_clauses_){
    // the last bit was only to choose the correct pool TODO if the encoding for the clause offsets changes, this line must be adjusted
    clause >>= 1;

    cache_.remove_damaged_entries(lit_pool.begin() + clause);
  }
  for(vector<LiteralID> clause: removed_long_clauses_){
    cache_.remove_damaged_entries(clause.begin());
  }
}



void ComponentManager::removeAllCachePollutionsOf(StackLevel &top) {
  // all processed components are found in
  // [top.currentRemainingComponent(), component_stack_.size())
  // first, remove the list of descendants from the father
  assert(top.remaining_components_ofs() <= component_stack_.size());
  assert(top.super_component() != 0);
  assert(cache_.hasEntry(superComponentOf(top).id()));

  if (top.remaining_components_ofs() == component_stack_.size()){
    return;
  }

  for (unsigned u = top.remaining_components_ofs(); u < component_stack_.size();
      u++) {
    assert(cache_.hasEntry(component_stack_[u]->id()));
    cache_.cleanPollutionsInvolving(component_stack_[u]->id());
  }

#ifdef DEBUG
  cache_.test_descendantstree_consistency();
#endif
}
