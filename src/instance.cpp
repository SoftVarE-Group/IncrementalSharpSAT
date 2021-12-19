/*
 * instance.cpp
 *
 *  Created on: Aug 23, 2012
 *      Author: Marc Thurley
 */

#include "instance.h"

#include <algorithm>
#include <fstream>
#include <sys/stat.h>

using namespace std;

Instance::Instance(){
  // clear everything
  original_literal_pool_.clear();
  original_literal_pool_.push_back(SENTINEL_LIT);
  conflict_literal_pool_.clear();
  conflict_literal_pool_.push_back(SENTINEL_LIT);

  variables_.clear();
  variables_.push_back(Variable()); //initializing the Sentinel
  literal_values_.clear();
  original_unit_clauses_.clear();
  conflict_unit_clauses_.clear();

  occurrence_lists_.clear();
  literals_.clear();
}


void Instance::cleanClause(ClauseOfs cl_ofs) {
  bool satisfied = false;
  for (auto it = beginOf(cl_ofs); *it != SENTINEL_LIT; it++)
    if (isSatisfied(*it)) {
      satisfied = true;
      break;
    }
  // mark the clause as empty if satisfied
  if (satisfied) {
    *beginOf(cl_ofs) = SENTINEL_LIT;
    return;
  }
  auto jt = beginOf(cl_ofs);
  auto it = beginOf(cl_ofs);
  // from now, all inactive literals are resolved
  for (; *it != SENTINEL_LIT; it++, jt++) {
    while (*jt != SENTINEL_LIT && !isActive(*jt))
      jt++;
    *it = *jt;
    if (*jt == SENTINEL_LIT)
      break;
  }
  unsigned length = it - beginOf(cl_ofs);
  // if it has become a unit clause, it should have already been asserted
  if (length == 1) {
    *beginOf(cl_ofs) = SENTINEL_LIT;
    // if it has become binary, transform it to binary and delete it
  } else if (length == 2) {
    addBinaryClause(*beginOf(cl_ofs), *(beginOf(cl_ofs) + 1), isConflictClause(cl_ofs));
    *beginOf(cl_ofs) = SENTINEL_LIT;
  } else{
    // even if it stayed longer than 2, it might still have gotten shorter
    getHeaderOf(cl_ofs).set_length(length);
  }
}

void Instance::compactClauses(bool clause_removal) {
  //these code pieces must not be repeated for the second literal pool
  for (auto &l : literals_)
      l.resetWatchList();
  occurrence_lists_.clear();
  occurrence_lists_.resize(variables_.size());
  conflict_clauses_.clear();
  clause_offset_translation_table_.clear();

  // runs first for orignal clauses, then for conflict clauses
  for(unsigned int working_on_conflict_clauses = false; working_on_conflict_clauses < 2; working_on_conflict_clauses++){
    vector<ClauseOfs> clause_ofs;
    clause_ofs.reserve(working_on_conflict_clauses ?  statistics_.num_long_conflict_clauses_ : statistics_.num_long_clauses_);

    // selects the appropriate literal pool
    vector<LiteralID>& literal_pool_ = working_on_conflict_clauses ?  conflict_literal_pool_ : original_literal_pool_;

    for (auto it_lit = literal_pool_.begin(); it_lit != literal_pool_.end();
        it_lit++) {
      if (*it_lit == SENTINEL_LIT) {
        if (it_lit + 1 == literal_pool_.end())
          break;
        it_lit += ClauseHeader::overheadInLits();

        // encodes working_on_conflict_clauses in final bit of the offset
        clause_ofs.push_back(((1 + it_lit - literal_pool_.begin()) << 1) | working_on_conflict_clauses);
      }
    }

    // prepares for clause_id_translation_table_, must be here because it needs the number of clauses
    unsigned int current_old_id = 0;
    unsigned int current_new_id = 0;
    if(!working_on_conflict_clauses){
      clause_id_translation_table_.clear();
      // the + 1 is because 0 marks the lack of a clause
      clause_id_translation_table_.resize(clause_ofs.size() + 1, 0);
    }

    if(!clause_removal){
      for (auto ofs : clause_ofs){
        cleanClause(ofs);
      }
    }else{
      for(ClauseOfs clause: (working_on_conflict_clauses ? removed_long_conflict_clauses_ : removed_long_original_clauses_)){
        // marking the clause to be removed. Has to be here because the marking inteferes with the creation of clause_ofs
        *beginOf(clause) = SENTINEL_LIT;
      }
    }

    vector<LiteralID> tmp_pool = literal_pool_;
    literal_pool_.clear();
    literal_pool_.push_back(SENTINEL_LIT);
    ClauseOfs new_ofs;
    unsigned num_clauses = 0;

    for (auto ofs : clause_ofs) {
      current_old_id++;

      //removes the final bit from ofs, as this encodes whether it is a conflict clause
      auto it = (tmp_pool.begin() + (ofs >> 1));
      if (*it != SENTINEL_LIT) {
        // copies the header
        for (auto jt = it - ClauseHeader::overheadInLits(); jt != it; jt++)
          literal_pool_.push_back(*jt);

        // encodes working_on_conflict_clauses in final bit of the offset
        new_ofs = (literal_pool_.size() << 1) | working_on_conflict_clauses;
        literal(*it).addWatchLinkTo(new_ofs);
        literal(*(it + 1)).addWatchLinkTo(new_ofs);
        num_clauses++;
        for (; *it != SENTINEL_LIT; it++) {
          literal_pool_.push_back(*it);

          // occurrence_lists_ should only contain original clauses
          if(!working_on_conflict_clauses){
            occurrence_lists_[*it].push_back(new_ofs);
          }
        }
        literal_pool_.push_back(SENTINEL_LIT);

        // both kinds of clauses have a clause offset
        clause_offset_translation_table_[ofs] = new_ofs;
        if(!working_on_conflict_clauses){
          // but only original clauses have a clause id
          current_new_id++;
          clause_id_translation_table_[current_old_id] = current_new_id;
        }
      }
    }

    if(!clause_removal){
      // selects which statistics entry to save the number of clauses in based on working_on_confilct_clauses
      working_on_conflict_clauses ?  statistics_.num_long_conflict_clauses_ : statistics_.num_long_clauses_ = num_clauses;

      vector<LiteralID> tmp_bin;
      unsigned bin_links = 0;
      for (auto &l : literals_) {
        tmp_bin.clear();
        // selects the appropriate literal list of binary links
        vector<LiteralID>& binary_links = working_on_conflict_clauses ? l.conflict_binary_links_ : l.original_binary_links_;
        for (auto it = binary_links.begin(); *it != SENTINEL_LIT; it++)
          if (isActive(*it))
            tmp_bin.push_back(*it);
        bin_links += tmp_bin.size();
        tmp_bin.push_back(SENTINEL_LIT);

        binary_links = tmp_bin;
      }
      // selects which statistics entry to save the number of clauses in based on working_on_confilct_clauses
      working_on_conflict_clauses ?  statistics_.num_binary_conflict_clauses_ : statistics_.num_binary_clauses_ = bin_links >> 1;
    }
  }
}

// void Instance::compactVariables() {
//   vector<unsigned> var_map(variables_.size(), 0);
//   unsigned last_ofs = 0;
//   unsigned num_isolated = 0;
//   LiteralIndexedVector<vector<LiteralID> > _tmp_bin_links(1);
//   LiteralIndexedVector<TriValue> _tmp_values = literal_values_;
//
//   for (auto l : literals_)
//     _tmp_bin_links.push_back(l.binary_links_);
//
//   assert(_tmp_bin_links.size() == literals_.size());
//   for (unsigned v = 1; v < variables_.size(); v++)
//     if (isActive(v)) {
//       if (isolated(v)) {
//         num_isolated++;
//         continue;
//       }
//       last_ofs++;
//       var_map[v] = last_ofs;
//     }
//
//   variables_.clear();
//   variables_.resize(last_ofs + 1);
//   occurrence_lists_.clear();
//   occurrence_lists_.resize(variables_.size());
//   literals_.clear();
//   literals_.resize(variables_.size());
//   literal_values_.clear();
//   literal_values_.resize(variables_.size(), X_TRI);
//
//   unsigned bin_links = 0;
//   LiteralID newlit;
//   for (auto l = LiteralID(0, false); l != _tmp_bin_links.end_lit(); l.inc()) {
//     if (var_map[l.var()] != 0) {
//       newlit = LiteralID(var_map[l.var()], l.sign());
//       for (auto it = _tmp_bin_links[l].begin(); *it != SENTINEL_LIT; it++) {
//         assert(var_map[it->var()] != 0);
//         literals_[newlit].addBinLinkTo(
//             LiteralID(var_map[it->var()], it->sign()));
//       }
//       bin_links += literals_[newlit].binary_links_.size() - 1;
//     }
//   }
//
//   vector<ClauseOfs> clause_ofs;
//   clause_ofs.reserve(statistics_.num_long_clauses_);
//   // clear watch links and occurrence lists
//   for (auto it_lit = literal_pool_.begin(); it_lit != literal_pool_.end();
//       it_lit++) {
//     if (*it_lit == SENTINEL_LIT) {
//       if (it_lit + 1 == literal_pool_.end())
//         break;
//       it_lit += ClauseHeader::overheadInLits();
//       clause_ofs.push_back(1 + it_lit - literal_pool_.begin());
//     }
//   }
//
//   for (auto ofs : clause_ofs) {
//     literal(LiteralID(var_map[beginOf(ofs)->var()], beginOf(ofs)->sign())).addWatchLinkTo(
//         ofs);
//     literal(LiteralID(var_map[(beginOf(ofs) + 1)->var()],
//             (beginOf(ofs) + 1)->sign())).addWatchLinkTo(ofs);
//     for (auto it_lit = beginOf(ofs); *it_lit != SENTINEL_LIT; it_lit++) {
//       *it_lit = LiteralID(var_map[it_lit->var()], it_lit->sign());
//       occurrence_lists_[*it_lit].push_back(ofs);
//     }
//   }
//
//   literal_values_.clear();
//   literal_values_.resize(variables_.size(), X_TRI);
//   unit_clauses_.clear();
//
//   statistics_.num_variables_ = variables_.size() - 1 + num_isolated;
//
//   statistics_.num_used_variables_ = num_variables();
//   statistics_.num_free_variables_ = num_isolated;
// }


void Instance::compactConflictLiteralPool(){
  auto write_pos = conflict_clauses_begin();
  vector<ClauseOfs> tmp_conflict_clauses = conflict_clauses_;
  conflict_clauses_.clear();
  for(auto clause_ofs: tmp_conflict_clauses){
    auto read_pos = beginOf(clause_ofs) - ClauseHeader::overheadInLits();
    for(unsigned i = 0; i < ClauseHeader::overheadInLits(); i++)
      *(write_pos++) = *(read_pos++);
    // stores 1 in final bit of offset to mark as conflict clause
    ClauseOfs new_ofs =  ((write_pos - conflict_literal_pool_.begin()) << 1) | 1;
    conflict_clauses_.push_back(new_ofs);
    // first substitute antecedent if clause_ofs implied something
    if(isAntecedentOf(clause_ofs, *beginOf(clause_ofs)))
      var(*beginOf(clause_ofs)).ante = Antecedent(new_ofs);

    // now redo the watches
    literal(*beginOf(clause_ofs)).replaceWatchLinkTo(clause_ofs,new_ofs);
    literal(*(beginOf(clause_ofs)+1)).replaceWatchLinkTo(clause_ofs,new_ofs);
    // next, copy clause data
    assert(read_pos == beginOf(clause_ofs));
    while(*read_pos != SENTINEL_LIT)
      *(write_pos++) = *(read_pos++);
    *(write_pos++) = SENTINEL_LIT;
  }
  conflict_literal_pool_.erase(write_pos,conflict_literal_pool_.end());
}

//bool Instance::deleteConflictClauses() {
//  statistics_.times_conflict_clauses_cleaned_++;
//  vector<ClauseOfs> tmp_conflict_clauses = conflict_clauses_;
//  conflict_clauses_.clear();
//  vector<double> tmp_ratios;
//  double score, lifetime;
//  for(auto clause_ofs: tmp_conflict_clauses){
//    score = getHeaderOf(clause_ofs).score();
//    lifetime = statistics_.num_conflicts_ - getHeaderOf(clause_ofs).creation_time();
//    tmp_ratios.push_back(score/lifetime/(getHeaderOf(clause_ofs).length()));
//  }
//  vector<double> tmp_ratiosB = tmp_ratios;
//
//  sort(tmp_ratiosB.begin(), tmp_ratiosB.end());
//
//  double cutoff = tmp_ratiosB[tmp_ratiosB.size()/2];
//
//  for(unsigned i = 0; i < tmp_conflict_clauses.size(); i++){
//    if(tmp_ratios[i] < cutoff){
//      if(!markClauseDeleted(tmp_conflict_clauses[i]))
//        conflict_clauses_.push_back(tmp_conflict_clauses[i]);
//    } else
//      conflict_clauses_.push_back(tmp_conflict_clauses[i]);
//  }
//  return true;
//}

bool Instance::deleteConflictClauses() {
  statistics_.times_conflict_clauses_cleaned_++;
  vector<ClauseOfs> tmp_conflict_clauses = conflict_clauses_;
  conflict_clauses_.clear();
  vector<double> tmp_ratios;
  double score, lifetime;
  for(auto clause_ofs: tmp_conflict_clauses){
    score = getHeaderOf(clause_ofs).score();
    lifetime = statistics_.num_total_conflicts_ - getHeaderOf(clause_ofs).creation_time();
   // tmp_ratios.push_back(score/lifetime);
    tmp_ratios.push_back(score);
  }
  vector<double> tmp_ratiosB = tmp_ratios;

  sort(tmp_ratiosB.begin(), tmp_ratiosB.end());

  double cutoff = tmp_ratiosB[tmp_ratiosB.size()/2];

  for(unsigned i = 0; i < tmp_conflict_clauses.size(); i++){
    if(tmp_ratios[i] < cutoff){
      if(!markClauseDeleted(tmp_conflict_clauses[i]))
        conflict_clauses_.push_back(tmp_conflict_clauses[i]);
      else{
        // a conflict clause was successfully marked as deleted
        statistics_.num_long_conflict_clauses_--;

        // the implication graph still has references to the clause
        removeFromImplicationGraph(tmp_conflict_clauses[i]);
      }
    } else
      conflict_clauses_.push_back(tmp_conflict_clauses[i]);
  }
  return true;
}


bool Instance::markClauseDeleted(ClauseOfs cl_ofs){
  // only first literal may possibly have cl_ofs as antecedent
  if(isAntecedentOf(cl_ofs, *beginOf(cl_ofs)))
    return false;

  literal(*beginOf(cl_ofs)).removeWatchLinkTo(cl_ofs);
  literal(*(beginOf(cl_ofs)+1)).removeWatchLinkTo(cl_ofs);
  return true;
}

void Instance::clearConflictClauses(){
  conflict_literal_pool_.clear();
  conflict_literal_pool_.push_back(SENTINEL_LIT);
  conflict_clauses_.clear();

  for(Literal &lit: literals_){
    vector<ClauseOfs> tmp_list = lit.watch_list_;
    lit.watch_list_.clear();
    for(ClauseOfs ofs : tmp_list){
      if(!isConflictClause(ofs)){
        lit.watch_list_.push_back(ofs);
      }
    }

    lit.conflict_binary_links_.clear();
    lit.conflict_binary_links_.push_back(SENTINEL_LIT);
  }

  conflict_unit_clauses_.clear();

  statistics_.num_long_conflict_clauses_ = 0;
  statistics_.num_binary_conflict_clauses_ = 0;
  statistics_.num_conflict_unit_clauses_ = 0;
}


void Instance::reserverVariables(unsigned int num_additional_vars){
  unsigned int nVars = num_variables() + num_additional_vars;

  variables_.resize(nVars + 1);
  literal_values_.resize(nVars + 1, X_TRI);
  occurrence_lists_.resize(nVars + 1);
  literals_.resize(nVars + 1);

  statistics_.num_variables_ = statistics_.num_original_variables_ = nVars;
}

void Instance::addClause(vector<LiteralID>& literals){
  auto write_pos = literals.begin();
  for(auto read_pos = literals.begin(); read_pos != literals.end(); read_pos++){
    // compares the literal at read_pos with all previous ones to find duplicates and tautologies
    bool found_duplicate = false;
    for(auto compared_literal = literals.begin(); compared_literal != write_pos; compared_literal++){
      if(compared_literal->neg() == *read_pos){
        // literal and its contradiction -> tautology, we can ignore the clause
        return;
      } else if(*compared_literal == *read_pos){
        found_duplicate = true;
        break;
      }
    }
    if(!found_duplicate){
        // literal is not a duplicate -> keep it
        *write_pos = *read_pos;
        write_pos++;
    }
  }

  // we only want the literals we intentionaly kept, which end at write_pos
  literals.erase(write_pos, literals.end());

  ClauseOfs cl_ofs = internalAddClause(literals, false);
  if (literals.size() > 2){
    added_long_clauses_.push_back(cl_ofs);

    for (auto l : literals)
      occurrence_lists_[l].push_back(cl_ofs);
  } else if (literals.size() == 2){
    //TODO adding a binary clause will fail if it already exists. Ignoring this will not affect correctness, but might decrease performance
    added_binary_clauses_.push_back(BinaryClause(literals[0], literals[1]));
  } else if(literals.size() == 1){
    added_unit_clauses_.push_back(literals[0]);
  }

  statistics_.num_original_clauses_++;
}

bool Instance::removeClause(vector<LiteralID>& clause_literals){
  //TODO this is copied from addClause, should be a function
  auto write_pos = clause_literals.begin();
  for(auto read_pos = clause_literals.begin(); read_pos != clause_literals.end(); read_pos++){
    // compares the literal at read_pos with all previous ones to find duplicates and tautologies
    bool found_duplicate = false;
    for(auto compared_literal = clause_literals.begin(); compared_literal != write_pos; compared_literal++){
      if(compared_literal->neg() == *read_pos){
        // literal and its contradiction -> tautology, we can ignore the clause
        return true;
      } else if(*compared_literal == *read_pos){
        found_duplicate = true;
        break;
      }
    }
    if(!found_duplicate){
        // literal is not a duplicate -> keep it
        *write_pos = *read_pos;
        write_pos++;
    }
  }
  // we only want the literals we intentionaly kept, which end at write_pos
  clause_literals.erase(write_pos, clause_literals.end());


  // the original removal might require us to remove further clauses, so we collect them on a stack
  vector<ClauseOfs> long_clause_stack;
  vector<BinaryClause> binary_clause_stack;
  vector<LiteralID> unit_clause_stack;

  // pushing the original clause onto its appropriate stack
  if(clause_literals.size() > 2){
    // we must find the clause first
    ClauseOfs clause = NOT_A_CLAUSE;
    // it must be in the occurence list of each of its literals, so we just pick one
    for(ClauseOfs clause_candidate : occurrence_lists_[clause_literals[0]]){
      // all the clauses in occurence_lists_ are original, so a check is not necessiary

      // we check the length first as this is a low-cost way to filter out some candidates
      if(getHeaderOf(clause_candidate).length() != clause_literals.size()){
        continue;
      } else{
        // as both clauses have the same size, they are equal if the candidate is a subset of literals
        bool equal = true;
        for(auto it = beginOf(clause_candidate); *it != SENTINEL_LIT; it++){
          bool found = false;
          for(LiteralID lit: clause_literals){
            if(lit == *it){
              found = true;
              break;
            }
          }

          if(!found){
            // not a subset, so the clauses can't be equal
            equal = false;
            break;
          }
        }
        if(equal){
          clause = clause_candidate;
          break;
        }
      }
    }

    if(clause == NOT_A_CLAUSE){
      //clause not found
      return false;
    }

    // we have found the clause
    long_clause_stack.push_back(clause);
  } else if(clause_literals.size() == 2){
    binary_clause_stack.push_back(BinaryClause(clause_literals[0], clause_literals[1]));
  } else if(clause_literals.size() == 1){
    unit_clause_stack.push_back(clause_literals[0]);
  }

  // working through the stacks. Because each removal can grow each stack, we cannot handle them in separate loops
  bool not_all_empty;
  // the first removal occurs on the original clauses, the other ones on the conflict clauses
  bool first_removal = true;
  do{
    not_all_empty = false;
    if(!long_clause_stack.empty()){
      ClauseOfs clause = long_clause_stack.back();
      long_clause_stack.pop_back();

      // we do not actually remove long clauses here, but do so in bulk at the beginning of the solving process
      (first_removal ? removed_long_original_clauses_ : removed_long_conflict_clauses_).push_back(clause);

      // we also store the content of the clause so we can still use it for cleanup after the removal
      auto clause_begin = beginOf(clause);
      // the +1 is to also include the closing SENTINEL_LIT
      removed_long_clause_literals_.push_back(vector<LiteralID>(clause_begin, clause_begin + getHeaderOf(clause).length() + 1));

      // we also need to remove any clauses implied by the current one
      if(long_clause_implication_links_.count(clause)){
        ClauseImplicationLinks& links = long_clause_implication_links_[clause];
        for(ClauseOfs cl: links.child_long_clauses_){
          long_clause_stack.push_back(cl);
        }
        for(BinaryClause cl: links.child_binary_clauses_){
          binary_clause_stack.push_back(cl);
        }
        for(LiteralID cl: links.child_unit_clauses_){
          unit_clause_stack.push_back(cl);
        }

        // with the clause removed, the links to it are no longer valid. We do not need to remove references for the children here as we will remove all their references later.
        for(ClauseOfs cl: links.parent_long_clauses_){
          // this is not guaranteed to be true as the parent was already removed if it was the clause which caused this removal
          if(long_clause_implication_links_.count(cl)){
            findAndErase(long_clause_implication_links_[cl].child_long_clauses_, clause);
          }
        }
        for(BinaryClause cl: links.child_binary_clauses_){
          // this is not guaranteed to be true as the parent was already removed if it was the clause which caused this removal
          if(binary_clause_implication_links_.count(cl)){
            findAndErase(binary_clause_implication_links_[cl].child_long_clauses_, clause);
          }
        }
        for(LiteralID cl: links.child_unit_clauses_){
          // this is not guaranteed to be true as the parent was already removed if it was the clause which caused this removal
          if(unit_clause_implication_links_.count(cl)){
            findAndErase(unit_clause_implication_links_[cl].child_long_clauses_, clause);
          }
        }
        // any links from the romeved clause are now invalid as well
        long_clause_implication_links_.erase(clause);

      }
      not_all_empty = true;
      first_removal = false;
    }
    if(!binary_clause_stack.empty()){
      BinaryClause clause = binary_clause_stack.back();
      binary_clause_stack.pop_back();

      removed_binary_clauses_.push_back(clause);

      // finding and removing the binary clause in the binary link lists
      // the first removal occurs on the original clauses, the other ones on the conflict clauses
      if(!(findAndErase(first_removal ? literal(clause.first).original_binary_links_ : literal(clause.first).conflict_binary_links_, clause.second, true)
        && findAndErase(first_removal ? literal(clause.second).original_binary_links_ : literal(clause.second).conflict_binary_links_, clause.first, true))){
        return false;
      }

      literal(clause.first).decreasePrevalence();
      literal(clause.second).decreasePrevalence();

      // we also need to remove any clauses implied by the current one
      if(binary_clause_implication_links_.count(clause)){
        ClauseImplicationLinks& links = binary_clause_implication_links_[clause];
        for(ClauseOfs cl: links.child_long_clauses_){
          long_clause_stack.push_back(cl);
        }
        for(BinaryClause cl: links.child_binary_clauses_){
          binary_clause_stack.push_back(cl);
        }
        for(LiteralID cl: links.child_unit_clauses_){
          unit_clause_stack.push_back(cl);
        }

        // with the clause removed, the links to it are no longer valid. We do not need to remove references for the children here as we will remove all their references later.
        for(ClauseOfs cl: links.parent_long_clauses_){
          // this is not guaranteed to be true as the parent was already removed if it was the clause which caused this removal
          if(long_clause_implication_links_.count(cl)){
            findAndErase(long_clause_implication_links_[cl].child_binary_clauses_, clause);
          }
        }
        for(BinaryClause cl: links.child_binary_clauses_){
          // this is not guaranteed to be true as the parent was already removed if it was the clause which caused this removal
          if(binary_clause_implication_links_.count(cl)){
            findAndErase(binary_clause_implication_links_[cl].child_binary_clauses_, clause);
          }
        }
        for(LiteralID cl: links.child_unit_clauses_){
          // this is not guaranteed to be true as the parent was already removed if it was the clause which caused this removal
          if(unit_clause_implication_links_.count(cl)){
            findAndErase(unit_clause_implication_links_[cl].child_binary_clauses_, clause);
          }
        }
        // any links from the romeved clause are now invalid as well
        binary_clause_implication_links_.erase(clause);
      }

      not_all_empty = true;
      first_removal = false;
    }
    if(!unit_clause_stack.empty()){
      LiteralID clause = unit_clause_stack.back();
      unit_clause_stack.pop_back();

      removed_unit_clauses_.push_back(clause);

      // finding and removing the unit clause in the unit clause list
      // the first removal occurs on the original clauses, the other ones on the conflict clauses
      if(!findAndErase(first_removal ? original_unit_clauses_ : conflict_unit_clauses_, clause)){
        return false;
      }

      // we also need to remove any clauses implied by the current one
      if(unit_clause_implication_links_.count(clause)){
        ClauseImplicationLinks& links = unit_clause_implication_links_[clause];
        for(ClauseOfs cl: links.child_long_clauses_){
          long_clause_stack.push_back(cl);
        }
        for(BinaryClause cl: links.child_binary_clauses_){
          binary_clause_stack.push_back(cl);
        }
        for(LiteralID cl: links.child_unit_clauses_){
          unit_clause_stack.push_back(cl);
        }

        // with the clause removed, the links to it are no longer valid. We do not need to remove references for the children here as we will remove all their references later.
        for(ClauseOfs cl: links.parent_long_clauses_){
          // this is not guaranteed to be true as the parent was already removed if it was the clause which caused this removal
          if(long_clause_implication_links_.count(cl)){
            findAndErase(long_clause_implication_links_[cl].child_unit_clauses_, clause);
          }
        }
        for(BinaryClause cl: links.child_binary_clauses_){
          // this is not guaranteed to be true as the parent was already removed if it was the clause which caused this removal
          if(binary_clause_implication_links_.count(cl)){
            findAndErase(binary_clause_implication_links_[cl].child_unit_clauses_, clause);
          }
        }
        for(LiteralID cl: links.child_unit_clauses_){
          // this is not guaranteed to be true as the parent was already removed if it was the clause which caused this removal
          if(unit_clause_implication_links_.count(cl)){
            findAndErase(unit_clause_implication_links_[cl].child_unit_clauses_, clause);
          }
        }
        // any links from the romeved clause are now invalid as well
        unit_clause_implication_links_.erase(clause);
      }

      not_all_empty = true;
      first_removal = false;
    }
  }while(not_all_empty);

  statistics_.incorporateClauseRemoval(clause_literals);
  statistics_.num_original_clauses_--;

  return true;
}


bool Instance::createfromFile(istream &input_file) {
  unsigned int nVars, nCls;
  unsigned int nRem = 0;
  int lit;
  unsigned max_ignore = 1000000;
  unsigned clauses_added = 0;
  unsigned clauses_removed = 0;
  LiteralID llit;
  vector<LiteralID> literals;
  string idstring;
  char c;

  //TODO these lines won't work with the new structure, but are related to a later TODO
//   struct stat filestatus;
//   stat(file_name.c_str(), &filestatus);

  literals.reserve(10000);
  while (input_file >> c && c != 'p' && c != 'a')
    input_file.ignore(max_ignore, '\n');

  // if assumptions exist, the previous while ended with c set to 'a'
  if(c == 'a'){
    // reads assumptions until closing 0 is reached
        assumptions_.clear();
    do{
      input_file >> lit;
            assumptions_.push_back(lit);
    }while(lit != 0);

    // move on to start of normal DIMACS
    input_file.ignore(max_ignore, 'p');
  }

  if (!(input_file >> idstring && idstring == "cnf" && input_file >> nVars
      && input_file >> nCls && (input_file.peek() == '\n' || input_file >> nRem))) {
    cerr << "Invalid CNF file" << endl;
    exit(0);
  }
  input_file.ignore(max_ignore, '\n');

  reserverVariables(nVars);

  //TODO the next three lines might be performance relevant, but they should not be placed here
  //TODO currently reserves the space originally intended for entire pool for both pools separately. Find better sizes
//   original_literal_pool_.reserve(filestatus.st_size);
//   conflict_literal_pool_.reserve(filestatus.st_size);
//   conflict_clauses_.reserve(2*nCls);

  while ((clauses_added < nCls || clauses_removed < nRem) && (input_file >> c)) {
    if ((c == '-') || isdigit(c)) {
      input_file.unget(); //extracted beginning of the clause to determine if we have a clause, so put it back
      literals.clear();
      while ((input_file >> lit) && lit != 0) {
        literals.push_back(lit);
      }
      assert(!literals.empty());
      clauses_added++;
      addClause(literals);
    } else if(c == 'r'){
      literals.clear();
      while ((input_file >> lit) && lit != 0) {
        literals.push_back(lit);
      }
      clauses_removed++;
      if(!removeClause(literals)){
        cerr << "Could not remove clause";
        for(LiteralID literal: literals){
          cerr << " " << literal.toInt();
        }
        cerr << endl;
      }
    }
    input_file.ignore(max_ignore, '\n');
  }

  return true;
}

void Instance::removeFromImplicationGraph(ClauseOfs ofs){
  ClauseImplicationLinks& links = long_clause_implication_links_[ofs];

  // replacing the clause with its children in its parents' links
  for(ClauseOfs parent: links.parent_long_clauses_){
    ClauseImplicationLinks& parent_links = long_clause_implication_links_[parent];
    findAndErase(parent_links.child_long_clauses_, ofs);
    for(ClauseOfs child: links.child_long_clauses_){
      parent_links.child_long_clauses_.push_back(child);
    }
    for(BinaryClause child: links.child_binary_clauses_){
      parent_links.child_binary_clauses_.push_back(child);
    }
    for(LiteralID child: links.child_unit_clauses_){
      parent_links.child_unit_clauses_.push_back(child);
    }
  }
  for(BinaryClause& parent: links.parent_binary_clauses_){
    ClauseImplicationLinks& parent_links = binary_clause_implication_links_[parent];
    findAndErase(parent_links.child_long_clauses_, ofs);
    for(ClauseOfs child: links.child_long_clauses_){
      parent_links.child_long_clauses_.push_back(child);
    }
    for(BinaryClause child: links.child_binary_clauses_){
      parent_links.child_binary_clauses_.push_back(child);
    }
    for(LiteralID child: links.child_unit_clauses_){
      parent_links.child_unit_clauses_.push_back(child);
    }
  }
  for(LiteralID parent: links.parent_unit_clauses_){
    ClauseImplicationLinks& parent_links = unit_clause_implication_links_[parent];
    findAndErase(parent_links.child_long_clauses_, ofs);
    for(ClauseOfs child: links.child_long_clauses_){
      parent_links.child_long_clauses_.push_back(child);
    }
    for(BinaryClause child: links.child_binary_clauses_){
      parent_links.child_binary_clauses_.push_back(child);
    }
    for(LiteralID child: links.child_unit_clauses_){
      parent_links.child_unit_clauses_.push_back(child);
    }
  }

  // replacing the clause with its parents in its children' links
  for(ClauseOfs child: links.child_long_clauses_){
    ClauseImplicationLinks& child_links = long_clause_implication_links_[child];
    findAndErase(child_links.parent_long_clauses_, ofs);
    for(ClauseOfs parent: links.parent_long_clauses_){
      child_links.parent_long_clauses_.push_back(parent);
    }
    for(BinaryClause parent: links.parent_binary_clauses_){
      child_links.parent_binary_clauses_.push_back(parent);
    }
    for(LiteralID parent: links.parent_unit_clauses_){
      child_links.parent_unit_clauses_.push_back(parent);
    }
  }
  for(BinaryClause child: links.child_binary_clauses_){
    ClauseImplicationLinks& child_links = binary_clause_implication_links_[child];
    findAndErase(child_links.parent_long_clauses_, ofs);
    for(ClauseOfs parent: links.parent_long_clauses_){
      child_links.parent_long_clauses_.push_back(parent);
    }
    for(BinaryClause parent: links.parent_binary_clauses_){
      child_links.parent_binary_clauses_.push_back(parent);
    }
    for(LiteralID parent: links.parent_unit_clauses_){
      child_links.parent_unit_clauses_.push_back(parent);
    }
  }
  for(LiteralID child: links.child_unit_clauses_){
    ClauseImplicationLinks& child_links = unit_clause_implication_links_[child];
    findAndErase(child_links.parent_long_clauses_, ofs);
    for(ClauseOfs parent: links.parent_long_clauses_){
      child_links.parent_long_clauses_.push_back(parent);
    }
    for(BinaryClause parent: links.parent_binary_clauses_){
      child_links.parent_binary_clauses_.push_back(parent);
    }
    for(LiteralID parent: links.parent_unit_clauses_){
      child_links.parent_unit_clauses_.push_back(parent);
    }
  }

}


