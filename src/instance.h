/*
 * instance.h
 *
 *  Created on: Aug 23, 2012
 *      Author: Marc Thurley
 */

#ifndef INSTANCE_H_
#define INSTANCE_H_

#include "statistics.h"
#include "structures.h"
#include "containers.h"
#include "clause_implication_links.h"

#include <unordered_map>

#include <assert.h>

class Instance {
public:
    Instance();

    // parses a formula from a DIMACS file. input_file must be an active stream with a valid DIMACS formula
    bool createfromFile(istream &input_file);

    //Increases the number of variables
    void reserverVariables(unsigned int num_additional_vars);

    void addClause(vector<LiteralID> &literals);
    // returns false if the clause was not found
    bool removeClause(vector<LiteralID> &literals);

    void setAssumptions(vector<LiteralID> &assumptions){
      this->assumptions_ = assumptions;
    }
protected:

  void unSet(LiteralID lit) {
    var(lit).ante = Antecedent(NOT_A_CLAUSE);
    var(lit).decision_level = INVALID_DL;
    literal_values_[lit] = X_TRI;
    literal_values_[lit.neg()] = X_TRI;
  }

  Antecedent & getAntecedent(LiteralID lit) {
    return variables_[lit.var()].ante;
  }

  bool hasAntecedent(LiteralID lit) {
    return variables_[lit.var()].ante.isAnt();
  }

  bool isAntecedentOf(ClauseOfs ante_cl, LiteralID lit) {
    return var(lit).ante.isAClause() && (var(lit).ante.asCl() == ante_cl);
  }

  bool isolated(VariableIndex v) {
    LiteralID lit(v, false);
    return (literal(lit).original_binary_links_.size() <= 1)
        & (literal(lit).conflict_binary_links_.size() <= 1)
        & occurrence_lists_[lit].empty()
        & (literal(lit.neg()).original_binary_links_.size() <= 1)
        & (literal(lit.neg()).conflict_binary_links_.size() <= 1)
        & occurrence_lists_[lit.neg()].empty();
  }

  bool free(VariableIndex v) {
    return isolated(v) & isActive(v);
  }

  bool deleteConflictClauses();
  bool markClauseDeleted(ClauseOfs cl_ofs);

  // Compact the literal pool erasing all the clause
  // information from deleted clauses
  void compactConflictLiteralPool();

  // we assert that the formula is consistent
  // and has not been found UNSAT yet
  // hard wires all assertions in the literal stack into the formula
  // removes all set variables and essentially reinitiallizes all
  // further data
  // if clause_removal is true, this method does not hardwire the assumptions
  // but instead applies the previously requested clause removals
  void compactClauses(bool clause_removal);
  void compactVariables();
  void cleanClause(ClauseOfs cl_ofs);

  void clearConflictClauses();

  /////////////////////////////////////////////////////////
  // END access to variables and literals
  /////////////////////////////////////////////////////////


  unsigned int num_conflict_clauses() const {
    return conflict_clauses_.size();
  }

  unsigned int num_variables() {
    return variables_.size() - 1;
  }

  DataAndStatistics statistics_;

  /** literal_pool_: the literals of all clauses are stored here
   *   INVARIANT: first and last entries of literal_pool_ are a SENTINEL_LIT
   *
   *   Clauses begin with a ClauseHeader structure followed by the literals
   *   terminated by SENTINEL_LIT
   */
  vector<LiteralID> original_literal_pool_;
  vector<LiteralID> conflict_literal_pool_;

  vector<LiteralID> assumptions_;

  vector<ClauseOfs> added_long_clauses_;
  vector<BinaryClause> added_binary_clauses_;
  vector<LiteralID> added_unit_clauses_;
  // separating the clauses according to the offset avoids redundant work in compact_clauses
  vector<ClauseOfs> removed_long_original_clauses_;
  vector<ClauseOfs> removed_long_conflict_clauses_;
  vector<vector<LiteralID>> removed_long_clause_literals_;
  vector<BinaryClause> removed_binary_clauses_;
  vector<LiteralID> removed_unit_clauses_;

  // these translate the clause identifiers into the new ones
  unordered_map<ClauseOfs, ClauseOfs> clause_offset_translation_table_;
  vector<unsigned int> clause_id_translation_table_;

  LiteralIndexedVector<Literal> literals_;

  LiteralIndexedVector<vector<ClauseOfs> > occurrence_lists_;

  vector<ClauseOfs> conflict_clauses_;

  vector<LiteralID> original_unit_clauses_;
  vector<LiteralID> conflict_unit_clauses_;

  vector<Variable> variables_;
  LiteralIndexedVector<TriValue> literal_values_;

  // if clause removal is combined with conflict clause reuse, we need to track implications
  unordered_map<ClauseOfs, ClauseImplicationLinks> long_clause_implication_links_;
  unordered_map<BinaryClause, ClauseImplicationLinks> binary_clause_implication_links_;
  unordered_map<LiteralID, ClauseImplicationLinks> unit_clause_implication_links_;

  void decayScores() {
    for (auto l_it = literals_.begin(); l_it != literals_.end(); l_it++){
      l_it->activity_score_ *= 0.5;
      l_it->prevalence_score_ *= 0.5;
    }

    for(auto clause_ofs: conflict_clauses_)
        getHeaderOf(clause_ofs).decayScore();

  }
//  void decayActivities();

  void updateActivities(ClauseOfs clause_ofs) {
    getHeaderOf(clause_ofs).increaseScore();
    for (auto it = beginOf(clause_ofs); *it != SENTINEL_LIT; it++) {
      literal(*it).increaseActivity();
    }
  }

  bool isUnitClause(const LiteralID lit) {
    for(unsigned int working_on_conflict_clauses = false; working_on_conflict_clauses < 2; working_on_conflict_clauses++){
      for (auto l : (working_on_conflict_clauses ? conflict_unit_clauses_ : original_unit_clauses_)){
        if (l == lit)
          return true;
      }
    }
    return false;
  }

  bool existsUnitClauseOf(VariableIndex v) {
    for(unsigned int working_on_conflict_clauses = false; working_on_conflict_clauses < 2; working_on_conflict_clauses++){
      for (auto l : (working_on_conflict_clauses ? conflict_unit_clauses_ : original_unit_clauses_)){
        if (l.var() == v)
          return true;
      }
    }
    return false;
  }

  // addUnitClause checks whether lit or lit.neg() is already a
  // unit clause
  // a negative return value implied that the Instance is UNSAT
  bool addUnitClause(const LiteralID lit, bool conflict) {
    for (auto l : (conflict ? conflict_unit_clauses_ : original_unit_clauses_)) {
      if (l == lit)
        return true;
      if (l == lit.neg())
        return false;
    }
    (conflict ? conflict_unit_clauses_ : original_unit_clauses_).push_back(lit);
    return true;
  }

  inline ClauseIndex internalAddClause (vector<LiteralID> &literals, bool conflict);

  // adds a UIP Conflict Clause
  // and returns it as an Antecedent to the first
  // literal stored in literals
  inline Antecedent addUIPConflictClause(vector<LiteralID> &literals, ClauseImplicationLinks& links);

  inline bool addBinaryClause(LiteralID litA, LiteralID litB, bool conflict);

  /////////////////////////////////////////////////////////
  // BEGIN access to variables, literals, clauses
  /////////////////////////////////////////////////////////

  inline Variable &var(const LiteralID lit) {
    return variables_[lit.var()];
  }

  Literal & literal(LiteralID lit) {
    return literals_[lit];
  }

  inline bool isSatisfied(const LiteralID &lit) const {
    return literal_values_[lit] == T_TRI;
  }

  bool isResolved(LiteralID lit) {
    return literal_values_[lit] == F_TRI;
  }

  bool isActive(LiteralID lit) const {
    return literal_values_[lit] == X_TRI;
  }

  inline bool isConflictClause(ClauseOfs cl_ofs) const{
    // the final bit encodes whether it is a conflict clause
    return cl_ofs & 1;
  }

  vector<LiteralID>::const_iterator beginOf(ClauseOfs cl_ofs) const {
    // selects the appropriate pool based on the final bit of cl_ofs, then drops this bit
    return (isConflictClause(cl_ofs) ? conflict_literal_pool_ : original_literal_pool_).begin() + (cl_ofs >> 1);
  }
  vector<LiteralID>::iterator beginOf(ClauseOfs cl_ofs) {
    // selects the appropriate pool based on the final bit of cl_ofs, then drops this bit
    return (isConflictClause(cl_ofs) ? conflict_literal_pool_ : original_literal_pool_).begin() + (cl_ofs >> 1);
  }

  decltype(conflict_literal_pool_.begin()) conflict_clauses_begin() {
     return conflict_literal_pool_.begin();
   }

  ClauseHeader &getHeaderOf(ClauseOfs cl_ofs) {
    // selects the appropriate pool based on the final bit of cl_ofs, then drops this bit
    return *reinterpret_cast<ClauseHeader *>(&(isConflictClause(cl_ofs) ? conflict_literal_pool_ : original_literal_pool_)
        [(cl_ofs >> 1) - ClauseHeader::overheadInLits()]);
  }

  bool isSatisfied(ClauseOfs cl_ofs) {
    for (auto lt = beginOf(cl_ofs); *lt != SENTINEL_LIT; lt++){
      if (isSatisfied(*lt))
        return true;
    }
    return false;
  }

  // if a clause is removed, without becoming invalid (i.e., to save memory), it needs to be removed from the implication graph while keeping its children
  void removeFromImplicationGraph(ClauseOfs ofs);
};

ClauseIndex Instance::internalAddClause (vector<LiteralID> &literals, bool conflict) {
  if(conflict){
    statistics_.incorporateConflictClauseData(literals);
  } else{
    statistics_.incorporateClauseData(literals);
  }

  if (literals.size() == 1) {
    //TODO Deal properly with the situation that opposing unit clauses are learned
    assert(!isUnitClause(literals[0].neg()));
    (conflict ? conflict_unit_clauses_ :  original_unit_clauses_).push_back(literals[0]);

    return 0;
  }
  if (literals.size() == 2) {
    addBinaryClause(literals[0], literals[1], conflict);

    return 0;
  }

  //selecting the appropriate literal pool
  vector<LiteralID>& literal_pool = conflict ? conflict_literal_pool_ : original_literal_pool_;

  for (unsigned i = 0; i < ClauseHeader::overheadInLits(); i++)
    literal_pool.push_back(0);

  // encoding conflict in the final bit
  ClauseOfs cl_ofs = (literal_pool.size() << 1) | conflict;

  for (auto l : literals) {
    literal_pool.push_back(l);
    literal(l).increasePrevalence(1);
  }
  // make an end: SENTINEL_LIT
  literal_pool.push_back(SENTINEL_LIT);
  literal(literals[0]).addWatchLinkTo(cl_ofs);
  literal(literals[1]).addWatchLinkTo(cl_ofs);
  getHeaderOf(cl_ofs).set_creation_time(statistics_.num_total_conflicts_ );
  getHeaderOf(cl_ofs).set_length(literals.size());

  return cl_ofs;
}


Antecedent Instance::addUIPConflictClause(vector<LiteralID> &literals, ClauseImplicationLinks& links) {
    Antecedent ante(NOT_A_CLAUSE);
    statistics_.num_total_clauses_learned_++;
    ClauseOfs cl_ofs = internalAddClause (literals, true);

    if (cl_ofs != 0) {
      conflict_clauses_.push_back(cl_ofs);

      // integrating the new clause into the implication tree
      long_clause_implication_links_[cl_ofs] = links;
      for(ClauseOfs parent: links.parent_long_clauses_){
        long_clause_implication_links_[parent].child_long_clauses_.push_back(cl_ofs);
      }
      for(BinaryClause parent: links.parent_binary_clauses_){
        binary_clause_implication_links_[parent].child_long_clauses_.push_back(cl_ofs);
      }
      for(LiteralID parent: links.parent_unit_clauses_){
        unit_clause_implication_links_[parent].child_long_clauses_.push_back(cl_ofs);
      }

      //TODO moved to internalAddClause, remove if no problems occur
      //getHeaderOf(cl_ofs).set_length(literals.size());

      ante = Antecedent(cl_ofs);
    } else if (literals.size() == 2){
      ante = Antecedent(literals.back());

      // integrating the new clause into the implication tree
      BinaryClause clause(literals[0], literals[1]);
      binary_clause_implication_links_[clause] = links;
      for(ClauseOfs parent: links.parent_long_clauses_){
        long_clause_implication_links_[parent].child_binary_clauses_.push_back(clause);
      }
      for(BinaryClause parent: links.parent_binary_clauses_){
        binary_clause_implication_links_[parent].child_binary_clauses_.push_back(clause);
      }
      for(LiteralID parent: links.parent_unit_clauses_){
        unit_clause_implication_links_[parent].child_binary_clauses_.push_back(clause);
      }
    } else if(literals.size() == 1){
      // integrating the new clause into the implication tree
      unit_clause_implication_links_[literals[0]] = links;
      for(ClauseOfs parent: links.parent_long_clauses_){
        long_clause_implication_links_[parent].child_unit_clauses_.push_back(literals[0]);
      }
      for(BinaryClause parent: links.parent_binary_clauses_){
        binary_clause_implication_links_[parent].child_unit_clauses_.push_back(literals[0]);
      }
      for(LiteralID parent: links.parent_unit_clauses_){
        unit_clause_implication_links_[parent].child_unit_clauses_.push_back(literals[0]);
      }
    }
    return ante;
  }

bool Instance::addBinaryClause(LiteralID litA, LiteralID litB, bool conflict) {
   if (literal(litA).hasBinaryLinkTo(litB))
     return false;
   literal(litA).addBinLinkTo(litB, conflict);
   literal(litB).addBinLinkTo(litA, conflict);
   literal(litA).increasePrevalence();
   literal(litB).increasePrevalence();
   return true;
}

// removes first occurence of toErase from vec. Swaps last entry to current position of to_erase instead of shifting entire rest of the vector.
// if keep_last_position is true, swaps in the second-to-last entry and keeps the previous last in the last postion
// retuns false if the toErease was not found
template<class T>
bool findAndErase(vector<T> &vec, T to_erase, bool keep_last_position = false){
  // searching the entry
  for(auto it = vec.begin(); it < vec.end(); it++){
    if(*it == to_erase){
      // found it. Replace it with the last entry, then delete the original position of that entry
      *it = vec.back();
      vec.pop_back();

      if(keep_last_position){
        // swapping the previously last entry with the previously second-to-last, so the former is now in the new last position
        swap(*it, vec.back());
      }

      // we are done. We only delete one occurrence if there are duplicates
      return true;
    }
  }

  // if we leave the loop, we did not find the entry
  return false;
}

#endif /* INSTANCE_H_ */


