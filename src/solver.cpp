/*
 * solver.cpp
 *
 *  Created on: Aug 23, 2012
 *      Author: marc
 */
#include "solver.h"
#include <deque>

#include <algorithm>


StopWatch::StopWatch() {
  interval_length_.tv_sec = 60;
  gettimeofday(&last_interval_start_, NULL);
  start_time_ = stop_time_ = last_interval_start_;
}

timeval StopWatch::getElapsedTime() {
  timeval r;
  timeval other_time = stop_time_;
  if (stop_time_.tv_sec == start_time_.tv_sec
      && stop_time_.tv_usec == start_time_.tv_usec)
    gettimeofday(&other_time, NULL);
  long int ad = 0;
  long int bd = 0;

  if (other_time.tv_usec < start_time_.tv_usec) {
    ad = 1;
    bd = 1000000;
  }
  r.tv_sec = other_time.tv_sec - ad - start_time_.tv_sec;
  r.tv_usec = other_time.tv_usec + bd - start_time_.tv_usec;
  return r;
}

void Solver::print(vector<LiteralID> &vec) {
	for (auto l : vec)
		cout << l.toInt() << " ";
	cout << endl;
}

void Solver::print(vector<unsigned> &vec) {
	for (auto l : vec)
		cout << l << " ";
	cout << endl;
}

bool Solver::simplePreProcess() {
	if (!config_.perform_pre_processing)
		return true;
	assert(literal_stack_.size() == 0);
	unsigned start_ofs = 0;
//BEGIN process unit clauses

    for(unsigned int working_on_conflict_clauses = false; working_on_conflict_clauses < 2; working_on_conflict_clauses++){
      for (auto lit : (working_on_conflict_clauses ?  conflict_unit_clauses_ : original_unit_clauses_)){
          if(isResolved(lit)){
              return false;
          } else{
              setLiteralIfFree(lit);
          }
      }
    }
//END process unit clauses
	bool succeeded = BCP(start_ofs);

	if (succeeded)
		succeeded &= prepFailedLiteralTest();

    // if clauses can be removed, we cannot change them
	if (succeeded && !config_.allow_clause_removal){
        HardWireAndCompact();
    }
	return succeeded;
}

bool Solver::prepFailedLiteralTest() {
	unsigned last_size;
	do {
		last_size = literal_stack_.size();
		for (unsigned v = 1; v < variables_.size(); v++)
			if (isActive(v)) {
				unsigned sz = literal_stack_.size();
				setLiteralIfFree(LiteralID(v, true));
				bool res = BCP(sz);
				while (literal_stack_.size() > sz) {
					unSet(literal_stack_.back());
					literal_stack_.pop_back();
				}

				if (!res) {
					sz = literal_stack_.size();
					setLiteralIfFree(LiteralID(v, false));
					if (!BCP(sz))
						return false;
				} else {

					sz = literal_stack_.size();
					setLiteralIfFree(LiteralID(v, false));
					bool resb = BCP(sz);
					while (literal_stack_.size() > sz) {
						unSet(literal_stack_.back());
						literal_stack_.pop_back();
					}
					if (!resb) {
						sz = literal_stack_.size();
						setLiteralIfFree(LiteralID(v, true));
						if (!BCP(sz))
							return false;
					}
				}
			}
	} while (literal_stack_.size() > last_size);

	return true;
}

void Solver::HardWireAndCompact() {
	compactClauses(false);

    // All current assignments need to be included in the unit clauses, as they may have caused their own cause to be removed
    // TODO this is somewhat inefficient
    for (auto &l : literal_stack_){
      addUnitClause(l, false);
    }

    // we may have renamed some clauses during compactClauses, so we need to fix existing references
    translate();

    // we do not want to remove variables, as they might reappear in incremental calls
    //compactVariables();

    literal_stack_.clear();

    statistics_.num_unit_clauses_ = original_unit_clauses_.size();
}

void Solver::translate(){
  // translating added clauses
  vector<ClauseOfs> tmp_clause_list = added_long_clauses_;
  added_long_clauses_.clear();
  for(ClauseOfs clause: tmp_clause_list){
    if(clause_offset_translation_table_[clause] != NOT_A_CLAUSE){
      added_long_clauses_.push_back(clause_offset_translation_table_[clause]);
    }
  }

  // we do not need to translate the removed clauses as they are no longer present at this point (they would therefore all become NOT_A_CLAUSE)

  // translating conflict clauses
  tmp_clause_list = conflict_clauses_;
  conflict_clauses_.clear();
  for(ClauseOfs clause: tmp_clause_list){
    if(clause_offset_translation_table_[clause] != NOT_A_CLAUSE){
      conflict_clauses_.push_back(clause_offset_translation_table_[clause]);
    }
  }

  // translating cache
  comp_manager_.translateCache(clause_id_translation_table_);

  // translating implications
  if(config_.track_implications()){
    // for the long clauses, the indices might no longer be valid
    unordered_map<ClauseOfs, ClauseImplicationLinks> tmp_long_clause_links = long_clause_implication_links_;
    long_clause_implication_links_.clear();
    for(pair<ClauseOfs, ClauseImplicationLinks> entry: tmp_long_clause_links){
      // assings the ClauseImplicationLinks to the translation of the previous index
      long_clause_implication_links_[clause_offset_translation_table_[entry.first]] = entry.second;
    }

    // the references to the long clauses might also have to be adjusted
    for(auto links_it = long_clause_implication_links_.begin(); links_it != long_clause_implication_links_.end(); links_it++){
      // translating references to parents
      for(auto entry_it = links_it->second.parent_long_clauses_.begin(); entry_it != links_it->second.parent_long_clauses_.end(); entry_it++){
        *entry_it = clause_offset_translation_table_[*entry_it];
      }

      // translating references to children
      for(auto entry_it = links_it->second.child_long_clauses_.begin(); entry_it != links_it->second.child_long_clauses_.end(); entry_it++){
        *entry_it = clause_offset_translation_table_[*entry_it];
      }
    }
    for(auto links_it = binary_clause_implication_links_.begin(); links_it != binary_clause_implication_links_.end(); links_it++){
      // translating references to parents
      for(auto entry_it = links_it->second.parent_long_clauses_.begin(); entry_it != links_it->second.parent_long_clauses_.end(); entry_it++){
        *entry_it = clause_offset_translation_table_[*entry_it];
      }

      // translating references to children
      for(auto entry_it = links_it->second.child_long_clauses_.begin(); entry_it != links_it->second.child_long_clauses_.end(); entry_it++){
        *entry_it = clause_offset_translation_table_[*entry_it];
      }
    }
    for(auto links_it = unit_clause_implication_links_.begin(); links_it != unit_clause_implication_links_.end(); links_it++){
      // translating references to parents
      for(auto entry_it = links_it->second.parent_long_clauses_.begin(); entry_it != links_it->second.parent_long_clauses_.end(); entry_it++){
        *entry_it = clause_offset_translation_table_[*entry_it];
      }

      // translating references to children
      for(auto entry_it = links_it->second.child_long_clauses_.begin(); entry_it != links_it->second.child_long_clauses_.end(); entry_it++){
        *entry_it = clause_offset_translation_table_[*entry_it];
      }
    }
  }
}


void Solver::earlyPrepare(){
  /*this also takes care of removing assignments between incremental calls.
  If you remove it, you must clean up manually */
  initStack(num_variables());

  // removes clauses
  if(config_.allow_clause_removal && (removed_long_original_clauses_.size() || removed_long_conflict_clauses_.size())){
    // actually removes the clauses in removed_long_clauses_
    compactClauses(true);
    // we may have renamed some clauses during compactClauses, so we need to fix existing references
    translate();
  }

  statistics_.prepare();
}

bool Solver::applyAssumptions(){
  for(auto lit: assumptions_){
    if(isResolved(lit)){
      // the assumption contradicts a previous assignment
      return false;
    }

    // as a starting point for BCP
    unsigned int assumption_offset = literal_stack_.size();

    // establish another decision stack level
    //TODO uses same values for super_comp and comp_stack_ofs as previous levels, probably fine, but check it properly
    stack_.push_back(StackLevel(1, literal_stack_.size(), 2));
    // we pretend to be in the second branch to prevent the assignment from being changed
    stack_.back().changeBranch();

    setLiteralIfFree(lit);
    if(!BCP(assumption_offset)){
      // propagating the assumption caused a contradiction
      return false;
    }
  }
  decision_level_after_assumptions_ = stack_.get_decision_level();

  /* repeating preprocessing steps after applying assumptions to take the added assignments into account.
  Cannot use HardWireAndCompact here because the assumptions are only temporary */
  if (!config_.perform_pre_processing)
      return true;
  else
    return prepFailedLiteralTest();
}

void Solver::latePrepare(){
  // the prevalence scores are only based on the current formula, so they are reset once that formula reaches its final state
  for (auto l = LiteralID(1, false); l != literals_.end_lit(); l.inc()) {
	literal(l).prevalence_score_ = literal(l).original_binary_links_.size() - 1;
	literal(l).prevalence_score_ += literal(l).conflict_binary_links_.size() - 1;
	literal(l).prevalence_score_ += occurrence_lists_[l].size();
  }

  last_ccl_deletion_time_ = last_ccl_cleanup_time_ = statistics_.num_total_clauses_learned_;

  violated_clause.reserve(num_variables());

  // the list for the cache cleanup does not contain the ClauseOfs of the removed clauses, as the translation has already taken care of that
  // not does it contain the removed unit clauses, as no component contains a unit clause anyway.
  comp_manager_.prepare(literals_, original_literal_pool_, added_long_clauses_, added_binary_clauses_, added_unit_clauses_, assumptions_, removed_long_clause_literals_, removed_binary_clauses_);

  // in the low cost version, the list is only updated once
  if(config_.variable_selection_adjustment == 1){
    updateVariablesInAddedClauses();
  }
}

void Solver::cleanup(){
  if(config_.adaptive_cache_limit){
    // we do not want to multiply the space taken by the infrastructure, only the space taken by the content
    config_.maximum_cache_size_bytes_ = config_.adaptive_cache_limit_factor_ * (statistics_.cache_bytes_memory_usage() - statistics_.cache_infrastructure_bytes_memory_usage_) + statistics_.cache_infrastructure_bytes_memory_usage_;

    // we do not want to change the maximum again, otherwise it could grow indefinitely
    config_.adaptive_cache_limit = false;
  }

  if(!config_.reuse_learned_clauses){
    clearConflictClauses();

    // reset increase of maximum number of learned clauses
    statistics_.times_conflict_clauses_cleaned_ = 0;
  }
  if(!config_.reuse_component_cache){
    comp_manager_.clear_cache();
  }
  if(!config_.reuse_literal_scores){
    comp_manager_.clear_scores();

    for (auto l = LiteralID(1, false); l != literals_.end_lit(); l.inc()) {
      // prevalence_score_ will be reset anyway, so it does not need to be here
      literal(l).activity_score_ = 0;
    }
  }

  added_long_clauses_.clear();
  added_binary_clauses_.clear();
  added_unit_clauses_.clear();
  removed_long_original_clauses_.clear();
  removed_long_conflict_clauses_.clear();
  removed_long_clause_literals_.clear();
  removed_binary_clauses_.clear();
  removed_unit_clauses_.clear();
  assumptions_.clear();
}

void Solver::updateVariablesInAddedClauses(){
  // resets variables_in_added_clauses_
  variables_in_added_clauses_.assign(num_variables() + 1, false);

  // variables in unit clauses
  for(LiteralID lit: added_unit_clauses_){
    variables_in_added_clauses_[lit.var()] = true;
  }

  // variables in binary clauses
  for(BinaryClause lits: added_binary_clauses_){
    variables_in_added_clauses_[lits.first.var()] = true;
    variables_in_added_clauses_[lits.second.var()] = true;
  }

  // variables in long clauses
  for(ClauseOfs cl: added_long_clauses_){
    // satisfied clauses are effectively removed -> we can ignore them
    if(!isSatisfied(cl)){
      for(auto current_lit = beginOf(cl); *current_lit != SENTINEL_LIT; current_lit++){
        variables_in_added_clauses_[current_lit->var()] = true;
      }
    }
  }
}


void Solver::solve() {
	stopwatch_.start();

    earlyPrepare();

	if (!config_.quiet) {
      if(!statistics_.input_file_.empty()){
		cout << "Solving " << statistics_.input_file_ << endl;
      } else {
        cout << "Solving formula" << endl;
      }
		statistics_.printShortFormulaInfo();
	}

	if (!config_.quiet)
		cout << endl << "Preprocessing .." << flush;

    bool notfoundUNSAT = simplePreProcess();

	if (!config_.quiet)
		cout << "DONE" << endl;

	if (notfoundUNSAT) {
		if (!config_.quiet) {
			statistics_.printShortFormulaInfo();
		}

		notfoundUNSAT = applyAssumptions();

        if(notfoundUNSAT){
          latePrepare();
          statistics_.time_for_preparations_ = stopwatch_.getElapsedSeconds();
          statistics_.store_reuse_data();

          statistics_.exit_state_ = countSAT();

          statistics_.set_final_solution_count(stack_.top().getTotalModelCount());
        } else {
            statistics_.exit_state_ = SUCCESS;
            statistics_.set_final_solution_count(0.0);

            if(!config_.quiet){
              cout << endl << "FOUND UNSAT WHILE APPLYING ASSUMPTIONS " << endl;
            }
        }
    } else {
		statistics_.exit_state_ = SUCCESS;
		statistics_.set_final_solution_count(0.0);

        if(!config_.quiet){
          cout << endl << "FOUND UNSAT DURING PREPROCESSING " << endl;
        }
	}

	cleanup();

	stopwatch_.stop();
	statistics_.time_elapsed_ = stopwatch_.getElapsedSeconds();

	comp_manager_.gatherStatistics();

    //TODO this method might need to be reworked to support a lack of an input file
	statistics_.writeToFile("data.out");
	if (!config_.quiet)
		statistics_.printShort();
}

SOLVER_StateT Solver::countSAT() {
	retStateT state = RESOLVED;

	while (true) {
		while (comp_manager_.findNextRemainingComponentOf(stack_.top())) {
			decideLiteral();
			if (stopwatch_.timeBoundBroken())
				return TIMEOUT;
			if (stopwatch_.interval_tick())
				printOnlineStats();

			while (!bcp()) {
				state = resolveConflict();
				if (state == BACKTRACK)
					break;
			}
			if (state == BACKTRACK)
				break;
		}

		state = backtrack();
		if (state == EXIT)
			return SUCCESS;
		while (state != PROCESS_COMPONENT && !bcp()) {
			state = resolveConflict();
			if (state == BACKTRACK) {
				state = backtrack();
				if (state == EXIT)
					return SUCCESS;
			}
		}
	}
	return SUCCESS;
}

void Solver::decideLiteral() {
    // in the high cost version, the list is updated whenever a literal is decided
    if(config_.variable_selection_adjustment == 2){
      updateVariablesInAddedClauses();
    }

	// establish another decision stack level
	stack_.push_back(
			StackLevel(stack_.top().currentRemainingComponent(),
					literal_stack_.size(),
					comp_manager_.component_stack_size()));

    bool can_choose_variable_from_new_clause = false;
	float max_score = -1;
	float score;
	unsigned max_score_var = 0;
	for (auto it = comp_manager_.superComponentOf(stack_.top()).varsBegin(); *it != varsSENTINEL; it++) {
        if(config_.variable_selection_adjustment){
            if(can_choose_variable_from_new_clause && !variables_in_added_clauses_[*it]){
                // variables from added clauses exists, but this isn't one of them -> skip
                continue;
            } else if(!can_choose_variable_from_new_clause && variables_in_added_clauses_[*it]){
                // this is the first variable from an addded clause -> now only such variables are allowed
                can_choose_variable_from_new_clause = true;
                // previous max came from  an illegal variable -> reset
                max_score = -1;
            }
        }

		score = scoreOf(*it);
		if (score > max_score) {
			max_score = score;
			max_score_var = *it;
		}
	}
	// this assert should always hold,
	// if not then there is a bug in the logic of countSAT();
	assert(max_score_var != 0);

	LiteralID theLit(max_score_var,
			literal(LiteralID(max_score_var, true)).totalScore()
					> literal(LiteralID(max_score_var, false)).totalScore());

	setLiteralIfFree(theLit);
	statistics_.num_total_decisions_++;

	if (statistics_.num_total_decisions_ % 128 == 0)
//    if (statistics_.num_conflicts_ % 128 == 0)
        decayScores();
       // decayActivitiesOf(comp_manager_.superComponentOf(stack_.top()));
	assert(
			stack_.top().remaining_components_ofs() <= comp_manager_.component_stack_size());
}

retStateT Solver::backtrack() {
	assert(
			stack_.top().remaining_components_ofs() <= comp_manager_.component_stack_size());
	do {
		if (stack_.top().branch_found_unsat())
			comp_manager_.removeAllCachePollutionsOf(stack_.top());
		else if (stack_.top().anotherCompProcessible())
			return PROCESS_COMPONENT;

		if (!stack_.top().isSecondBranch()) {
			LiteralID aLit = TOS_decLit();
			assert(stack_.get_decision_level() > 0);
			stack_.top().changeBranch();
			reactivateTOS();
			setLiteralIfFree(aLit.neg(), NOT_A_CLAUSE);
			return RESOLVED;
		}
		// OTHERWISE:  backtrack further
		comp_manager_.cacheModelCountOf(stack_.top().super_component(),
				stack_.top().getTotalModelCount());

		if (stack_.get_decision_level() <= decision_level_after_assumptions_)
			break;
		reactivateTOS();

		assert(stack_.size()>=2);
		(stack_.end() - 2)->includeSolution(stack_.top().getTotalModelCount());
		stack_.pop_back();
		// step to the next component not yet processed
		stack_.top().nextUnprocessedComponent();

		assert(
				stack_.top().remaining_components_ofs() < comp_manager_.component_stack_size()+1);

    /* this seems to always be true, because there is a break if decision_level is not larger
    than 0 (now decision_level_after_assumptions_), and only one level is removed afterwards */
	} while (stack_.get_decision_level() >= 0);
	return EXIT;
}

retStateT Solver::resolveConflict() {
	recordLastUIPCauses();

	if (statistics_.num_total_clauses_learned_ - last_ccl_deletion_time_
			> statistics_.clause_deletion_interval()) {
		deleteConflictClauses();
		last_ccl_deletion_time_ = statistics_.num_total_clauses_learned_;
	}

	if (statistics_.num_total_clauses_learned_ - last_ccl_cleanup_time_ > 100000) {
		compactConflictLiteralPool();
		last_ccl_cleanup_time_ = statistics_.num_total_clauses_learned_;
	}

	statistics_.num_total_conflicts_++;

	assert(
			stack_.top().remaining_components_ofs() <= comp_manager_.component_stack_size());

	assert(uip_clauses_.size() == 1);

	// DEBUG
	if (uip_clauses_.back().size() == 0)
		cout << " EMPTY CLAUSE FOUND" << endl;
	// END DEBUG

	stack_.top().mark_branch_unsat();
	//BEGIN Backtracking
	// maybe the other branch had some solutions
	if (stack_.top().isSecondBranch()) {
		return BACKTRACK;
	}

	Antecedent ant(NOT_A_CLAUSE);
	// this has to be checked since using implicit BCP
	// and checking literals there not exhaustively
	// we cannot guarantee that uip_clauses_.back().front() == TOS_decLit().neg()
	// this is because we might have checked a literal
	// during implict BCP which has been a failed literal
	// due only to assignments made at lower decision levels
	if (uip_clauses_.back().front() == TOS_decLit().neg()) {
		assert(TOS_decLit().neg() == uip_clauses_.back()[0]);
		var(TOS_decLit().neg()).ante = addUIPConflictClause(
				uip_clauses_.back(), uip_clause_implication_links_.back());
		ant = var(TOS_decLit()).ante;
	}
//	// RRR
//	else if(var(uip_clauses_.back().front()).decision_level
//			< stack_.get_decision_level()
//			&& assertion_level_ <  stack_.get_decision_level()){
//         stack_.top().set_both_branches_unsat();
//         return BACKTRACK;
//	}
//
//
//	// RRR
	assert(stack_.get_decision_level() > 0);
	assert(stack_.top().branch_found_unsat());

	// we do not have to remove pollutions here,
	// since conflicts only arise directly before
	// remaining components are stored
	// hence
	assert(
			stack_.top().remaining_components_ofs() == comp_manager_.component_stack_size());

	stack_.top().changeBranch();
	LiteralID lit = TOS_decLit();
	reactivateTOS();
	setLiteralIfFree(lit.neg(), ant);
//END Backtracking
	return RESOLVED;
}

bool Solver::bcp() {
// the asserted literal has been set, so we start
// bcp on that literal
	unsigned start_ofs = literal_stack_.size() - 1;

//BEGIN process unit clauses

    for(unsigned int working_on_conflict_clauses = false; working_on_conflict_clauses < 2; working_on_conflict_clauses++){
      for (auto lit : (working_on_conflict_clauses ? conflict_unit_clauses_ : original_unit_clauses_)){
          if(isResolved(lit)){

          }else{
            setLiteralIfFree(lit);
          }
      }
    }
//END process unit clauses

	bool bSucceeded = BCP(start_ofs);

	if (config_.perform_failed_lit_test && bSucceeded) {
		bSucceeded = implicitBCP();
	}

	return bSucceeded;
}

bool Solver::BCP(unsigned start_at_stack_ofs) {
	for (unsigned int i = start_at_stack_ofs; i < literal_stack_.size(); i++) {
		LiteralID unLit = literal_stack_[i].neg();
		//BEGIN Propagate Bin Clauses
        // runs first for orignal clauses, then for conflict clauses
        for(unsigned int working_on_conflict_clauses = false; working_on_conflict_clauses < 2; working_on_conflict_clauses++){
          // selects the appropriate literal list of binary links
          vector<LiteralID>& binary_links = (working_on_conflict_clauses ? literal(unLit).conflict_binary_links_ : literal(unLit).original_binary_links_);
          for (auto bt = binary_links.begin();
                  *bt != SENTINEL_LIT; bt++) {
              if (isResolved(*bt)) {
                  setConflictState(unLit, *bt);
                  return false;
              }
              setLiteralIfFree(*bt, Antecedent(unLit));
          }
        }
		//END Propagate Bin Clauses

		for (auto itcl = literal(unLit).watch_list_.rbegin();
				*itcl != SENTINEL_CL; itcl++) {
			bool isLitA = (*beginOf(*itcl) == unLit);
			auto p_watchLit = beginOf(*itcl) + 1 - isLitA;
			auto p_otherLit = beginOf(*itcl) + isLitA;

			if (isSatisfied(*p_otherLit))
				continue;
			auto itL = beginOf(*itcl) + 2;
			while (isResolved(*itL))
				itL++;

			// either we found a free or satisfied lit
			if (*itL != SENTINEL_LIT) {
				literal(*itL).addWatchLinkTo(*itcl);
				swap(*itL, *p_watchLit);
				*itcl = literal(unLit).watch_list_.back();
				literal(unLit).watch_list_.pop_back();
			} else {
				// or p_unLit stays resolved
				// and we have hence no free literal left
				// for p_otherLit remain poss: Active or Resolved
				if (setLiteralIfFree(*p_otherLit, Antecedent(*itcl))) { // implication
					if (isLitA)
						swap(*p_otherLit, *p_watchLit);
				} else {
					setConflictState(*itcl);
					return false;
				}
			}
		}
	}
	return true;
}

//bool Solver::implicitBCP() {
//  static vector<LiteralID> test_lits(num_variables());
//  static LiteralIndexedVector<unsigned char> viewed_lits(num_variables() + 1,
//      0);
//
//  unsigned stack_ofs = stack_.top().literal_stack_ofs();
//  while (stack_ofs < literal_stack_.size()) {
//    test_lits.clear();
//    for (auto it = literal_stack_.begin() + stack_ofs;
//        it != literal_stack_.end(); it++) {
//      for (auto cl_ofs : occurrence_lists_[it->neg()])
//        if (!isSatisfied(cl_ofs)) {
//          for (auto lt = beginOf(cl_ofs); *lt != SENTINEL_LIT; lt++)
//            if (isActive(*lt) && !viewed_lits[lt->neg()]) {
//              test_lits.push_back(lt->neg());
//              viewed_lits[lt->neg()] = true;
//
//            }
//        }
//    }
//
//    stack_ofs = literal_stack_.size();
//    for (auto jt = test_lits.begin(); jt != test_lits.end(); jt++)
//      viewed_lits[*jt] = false;
//
//    statistics_.num_failed_literal_tests_ += test_lits.size();
//
//    for (auto lit : test_lits)
//      if (isActive(lit)) {
//        unsigned sz = literal_stack_.size();
//        // we increase the decLev artificially
//        // s.t. after the tentative BCP call, we can learn a conflict clause
//        // relative to the assignment of *jt
//        stack_.startFailedLitTest();
//        setLiteralIfFree(lit);
//
//        assert(!hasAntecedent(lit));
//
//        bool bSucceeded = BCP(sz);
//        if (!bSucceeded)
//          recordAllUIPCauses();
//
//        stack_.stopFailedLitTest();
//
//        while (literal_stack_.size() > sz) {
//          unSet(literal_stack_.back());
//          literal_stack_.pop_back();
//        }
//
//        if (!bSucceeded) {
//        	statistics_.num_failed_literals_detected_++;
//          sz = literal_stack_.size();
//          for (auto it = uip_clauses_.rbegin(); it != uip_clauses_.rend();
//              it++) {
//            setLiteralIfFree(it->front(), addUIPConflictClause(*it));
//          }
//          if (!BCP(sz))
//            return false;
//        }
//      }
//  }
//  return true;
//}

// this is IBCP 30.08
bool Solver::implicitBCP() {
    // keeping these static will avoid needless reallocations. Needed reallocations are triggerd by the resizes
	static vector<LiteralID> test_lits;
    test_lits.resize(num_variables());
	static LiteralIndexedVector<unsigned char> viewed_lits;
    viewed_lits.resize(num_variables() + 1,	0);

	unsigned stack_ofs = stack_.top().literal_stack_ofs();
	unsigned num_curr_lits = 0;
	while (stack_ofs < literal_stack_.size()) {
		test_lits.clear();
		for (auto it = literal_stack_.begin() + stack_ofs;
				it != literal_stack_.end(); it++) {
            for (auto cl_ofs : occurrence_lists_[it->neg()]){
				if (!isSatisfied(cl_ofs)) {
					for (auto lt = beginOf(cl_ofs); *lt != SENTINEL_LIT; lt++){
                		if (isActive(*lt) && !viewed_lits[lt->neg()]) {
							test_lits.push_back(lt->neg());
							viewed_lits[lt->neg()] = true;
                        }
                    }
				}
            }
		}
		num_curr_lits = literal_stack_.size() - stack_ofs;
		stack_ofs = literal_stack_.size();
		for (auto jt = test_lits.begin(); jt != test_lits.end(); jt++)
			viewed_lits[*jt] = false;

		vector<float> scores;
		scores.clear();
		for (auto jt = test_lits.begin(); jt != test_lits.end(); jt++) {
			scores.push_back(literal(*jt).totalScore());
		}
		sort(scores.begin(), scores.end());
		num_curr_lits = 10 + num_curr_lits / 20;
		float threshold = 0.0;
		if (scores.size() > num_curr_lits) {
			threshold = scores[scores.size() - num_curr_lits];
		}

		statistics_.num_failed_literal_tests_ += test_lits.size();

		for (auto lit : test_lits)
			if (isActive(lit) && threshold <= literal(lit).totalScore()) {
				unsigned sz = literal_stack_.size();
				// we increase the decLev artificially
				// s.t. after the tentative BCP call, we can learn a conflict clause
				// relative to the assignment of *jt
				stack_.startFailedLitTest();
				setLiteralIfFree(lit);

				assert(!hasAntecedent(lit));

				bool bSucceeded = BCP(sz);
				if (!bSucceeded){
					recordAllUIPCauses();
                }

				stack_.stopFailedLitTest();

				while (literal_stack_.size() > sz) {
					unSet(literal_stack_.back());
					literal_stack_.pop_back();
				}

				if (!bSucceeded) {
					statistics_.num_failed_literals_detected_++;
					sz = literal_stack_.size();
                    auto links = uip_clause_implication_links_.rbegin();
					for (auto it = uip_clauses_.rbegin();
							it != uip_clauses_.rend(); it++, links++) {
						// DEBUG
						if (it->size() == 0)
							cout << "EMPTY CLAUSE FOUND" << endl;
						// END DEBUG
						setLiteralIfFree(it->front(),
								addUIPConflictClause(*it, *links));
					}
					if (!BCP(sz))
						return false;
				}
			}
	}

	// BEGIN TEST
//	float max_score = -1;
//	float score;
//	unsigned max_score_var = 0;
//	for (auto it =
//			component_analyzer_.superComponentOf(stack_.top()).varsBegin();
//			*it != varsSENTINEL; it++)
//		if (isActive(*it)) {
//			score = scoreOf(*it);
//			if (score > max_score) {
//				max_score = score;
//				max_score_var = *it;
//			}
//		}
//	LiteralID theLit(max_score_var,
//			literal(LiteralID(max_score_var, true)).activity_score_
//					> literal(LiteralID(max_score_var, false)).activity_score_);
//	if (!fail_test(theLit.neg())) {
//		cout << ".";
//
//		statistics_.num_failed_literals_detected_++;
//		unsigned sz = literal_stack_.size();
//		for (auto it = uip_clauses_.rbegin(); it != uip_clauses_.rend(); it++) {
//			setLiteralIfFree(it->front(), addUIPConflictClause(*it));
//		}
//		if (!BCP(sz))
//			return false;
//
//	}
	// END
	return true;
}

///////////////////////////////////////////////////////////////////////////////////////////////
// BEGIN module conflictAnalyzer
///////////////////////////////////////////////////////////////////////////////////////////////

void Solver::minimizeAndStoreUIPClause(LiteralID uipLit,
		vector<LiteralID> & tmp_clause, bool seen[]) {
	static deque<LiteralID> clause;
	clause.clear();
	assertion_level_ = 0;
	for (auto lit : tmp_clause) {
		if (existsUnitClauseOf(lit.var()))
			continue;
		bool resolve_out = false;
		if (hasAntecedent(lit)) {
			resolve_out = true;
			if (getAntecedent(lit).isAClause()) {
				for (auto it = beginOf(getAntecedent(lit).asCl()) + 1;
						*it != SENTINEL_CL; it++)
					if (!seen[it->var()]) {
						resolve_out = false;
						break;
					}
			} else if (!seen[getAntecedent(lit).asLit().var()]) {
				resolve_out = false;
			}
		}

		if (!resolve_out) {
			// uipLit should be the sole literal of this Decision Level
			if (var(lit).decision_level >= assertion_level_) {
				assertion_level_ = var(lit).decision_level;
				clause.push_front(lit);
			} else
				clause.push_back(lit);
		}
	}

	if(uipLit.var())
	 assert(var(uipLit).decision_level == stack_.get_decision_level());

	//assert(uipLit.var() != 0);
	if (uipLit.var() != 0)
		clause.push_front(uipLit);
	uip_clauses_.push_back(vector<LiteralID>(clause.begin(), clause.end()));
}

void Solver::recordLastUIPCauses() {
// note:
// variables of lower dl: if seen we dont work with them anymore
// variables of this dl: if seen we incorporate their
// antecedent and set to unseen
	bool seen[num_variables() + 1];
	memset(seen, false, sizeof(bool) * (num_variables() + 1));

	static vector<LiteralID> tmp_clause;
	tmp_clause.clear();

	assertion_level_ = 0;
	uip_clauses_.clear();

	unsigned lit_stack_ofs = literal_stack_.size();
	int DL = stack_.get_decision_level();
	unsigned lits_at_current_dl = 0;

    // the implication links for the currently created clause
    ClauseImplicationLinks links;

    uip_clause_implication_links_.clear();

    // violated clause is among the clauses implying the new clause
    if(config_.track_implications()){
      if(violated_clause_ofs != NOT_A_CLAUSE){
        // violated_clause is a long clause
        links.parent_long_clauses_.push_back(violated_clause_ofs);
      } else{
        // violated_clause is a binary clause
        links.parent_binary_clauses_.push_back(BinaryClause(violated_clause[0], violated_clause[1]));
      }
    }

	for (auto l : violated_clause) {
        // we need to differentiate these cases because when tracking links, we cannot consider preprocessing assignments as unit clauses (TODO unless we track their cause)
        if(config_.track_implications()){
          if(existsUnitClauseOf(l.var())){
            // the unit clause is part of the implying clause set.
            links.parent_unit_clauses_.push_back(l);
            continue;
          }
        } else if(var(l).decision_level == 0 || existsUnitClauseOf(l.var())){
            continue;
        }
		if (var(l).decision_level < DL)
			tmp_clause.push_back(l);
		else
			lits_at_current_dl++;
		literal(l).increaseActivity();
		seen[l.var()] = true;
	}

	LiteralID curr_lit;
	while (lits_at_current_dl) {
		assert(lit_stack_ofs != 0);
		curr_lit = literal_stack_[--lit_stack_ofs];

		if (!seen[curr_lit.var()])
			continue;

		seen[curr_lit.var()] = false;

		if (lits_at_current_dl-- == 1) {
			// perform UIP stuff
			if (!hasAntecedent(curr_lit)) {
				// this should be the decision literal when in first branch
				// or it is a literal decided to explore in failed literal testing
				//assert(stack_.TOS_decLit() == curr_lit);
//				cout << "R" << curr_lit.toInt() << "S"
//				     << var(curr_lit).ante.isAnt() << " "  << endl;
				break;
			}
		}

		assert(hasAntecedent(curr_lit));

		//cout << "{" << curr_lit.toInt() << "}";
		if (getAntecedent(curr_lit).isAClause()) {
			updateActivities(getAntecedent(curr_lit).asCl());
			assert(curr_lit == *beginOf(getAntecedent(curr_lit).asCl()));

            if(config_.track_implications()){
              // the long clause is part of the implying clause set
              links.parent_long_clauses_.push_back(getAntecedent(curr_lit).asCl());
            }

			for (auto it = beginOf(getAntecedent(curr_lit).asCl()) + 1;
					*it != SENTINEL_CL; it++) {
				if (seen[it->var()]){
                  continue;
                }
                // we need to differentiate these cases because when tracking links, we cannot consider preprocessing assignments as unit clauses (TODO unless we track their cause)
                if(config_.track_implications()){
                  if(existsUnitClauseOf(it->var())){
                    // the unit clause is part of the implying clause set.
                    links.parent_unit_clauses_.push_back(*it);
                    continue;
                  }
                } else if ((var(*it).decision_level == 0)|| existsUnitClauseOf(it->var())){
					continue;
                }
				if (var(*it).decision_level < DL)
					tmp_clause.push_back(*it);
				else
					lits_at_current_dl++;
				seen[it->var()] = true;
			}
		} else {
			LiteralID alit = getAntecedent(curr_lit).asLit();
			literal(alit).increaseActivity();
			literal(curr_lit).increaseActivity();

            if(config_.track_implications()){
              // the binary clause is part of the implying clause set.
              links.parent_binary_clauses_.push_back(BinaryClause(alit, curr_lit));
            }

			if (!seen[alit.var()] && (!(var(alit).decision_level == 0) || config_.track_implications())){
              if(!existsUnitClauseOf(alit.var())) {
                  if (var(alit).decision_level < DL)
                      tmp_clause.push_back(alit);
                  else
                      lits_at_current_dl++;
                  seen[alit.var()] = true;
              } else if(config_.track_implications()){
                // the unit clause is part of the implying clause set.
                links.parent_unit_clauses_.push_back(alit);
              }
			}
		}
		curr_lit = NOT_A_LIT;
	}

//	cout << "T" << curr_lit.toInt() << "U "
//     << var(curr_lit).decision_level << ", " << stack_.get_decision_level() << endl;
//	cout << "V"  << var(curr_lit).ante.isAnt() << " "  << endl;
	minimizeAndStoreUIPClause(curr_lit.neg(), tmp_clause, seen);
    uip_clause_implication_links_.push_back(links);

//	if (var(curr_lit).decision_level > assertion_level_)
//		assertion_level_ = var(curr_lit).decision_level;
}

void Solver::recordAllUIPCauses() {
// note:
// variables of lower dl: if seen we dont work with them anymore
// variables of this dl: if seen we incorporate their
// antecedent and set to unseen
	bool seen[num_variables() + 1];
	memset(seen, false, sizeof(bool) * (num_variables() + 1));

	static vector<LiteralID> tmp_clause;
	tmp_clause.clear();

	assertion_level_ = 0;
	uip_clauses_.clear();

	unsigned lit_stack_ofs = literal_stack_.size();
	int DL = stack_.get_decision_level();
	unsigned lits_at_current_dl = 0;

     // the implication links for the currently created clause
    ClauseImplicationLinks links;

    uip_clause_implication_links_.clear();

    // violated clause is among the clauses implying the new clause
    if(config_.track_implications()){
      if(violated_clause_ofs != NOT_A_CLAUSE){
        // violated_clause is a long clause
        links.parent_long_clauses_.push_back(violated_clause_ofs);
      } else{
        // violated_clause is a binary clause
        links.parent_binary_clauses_.push_back(BinaryClause(violated_clause[0], violated_clause[1]));
      }
    }

	for (auto l : violated_clause) {
		// we need to differentiate these cases because when tracking links, we cannot consider preprocessing assignments as unit clauses (TODO unless we track their cause)
        if(config_.track_implications()){
          if(existsUnitClauseOf(l.var())){
            // the unit clause is part of the implying clause set.
            links.parent_unit_clauses_.push_back(l);
            continue;
          }
        } else if(var(l).decision_level == 0 || existsUnitClauseOf(l.var())){
            continue;
        }
		if (var(l).decision_level < DL)
			tmp_clause.push_back(l);
		else
			lits_at_current_dl++;
		literal(l).increaseActivity();
		seen[l.var()] = true;
	}
	unsigned n = 0;
	LiteralID curr_lit;
	while (lits_at_current_dl) {
		assert(lit_stack_ofs != 0);
		curr_lit = literal_stack_[--lit_stack_ofs];

		if (!seen[curr_lit.var()])
			continue;

		seen[curr_lit.var()] = false;

		if (lits_at_current_dl-- == 1) {
			n++;
			if (!hasAntecedent(curr_lit)) {
				// this should be the decision literal when in first branch
				// or it is a literal decided to explore in failed literal testing
				//assert(stack_.TOS_decLit() == curr_lit);
				break;
			}
			// perform UIP stuff
			minimizeAndStoreUIPClause(curr_lit.neg(), tmp_clause, seen);
            uip_clause_implication_links_.push_back(links);
		}

		assert(hasAntecedent(curr_lit));

		if (getAntecedent(curr_lit).isAClause()) {
			updateActivities(getAntecedent(curr_lit).asCl());
			assert(curr_lit == *beginOf(getAntecedent(curr_lit).asCl()));

            if(config_.track_implications()){
              // the long clause is part of the implying clause set
              links.parent_long_clauses_.push_back(getAntecedent(curr_lit).asCl());
            }

			for (auto it = beginOf(getAntecedent(curr_lit).asCl()) + 1;
					*it != SENTINEL_CL; it++) {
				if (seen[it->var()]){
                  continue;
                }
                // we need to differentiate these cases because when tracking links, we cannot consider preprocessing assignments as unit clauses (TODO unless we track their cause)
                if(config_.track_implications()){
                  if(existsUnitClauseOf(it->var())){
                    // the unit clause is part of the implying clause set.
                    links.parent_unit_clauses_.push_back(*it);
                    continue;
                  }
                } else if ((var(*it).decision_level == 0)|| existsUnitClauseOf(it->var())){
					continue;
                }
				if (var(*it).decision_level < DL)
					tmp_clause.push_back(*it);
				else
					lits_at_current_dl++;
				seen[it->var()] = true;
			}
		} else {
			LiteralID alit = getAntecedent(curr_lit).asLit();
			literal(alit).increaseActivity();
			literal(curr_lit).increaseActivity();

            if(config_.track_implications()){
              // the binary clause is part of the implying clause set.
              links.parent_binary_clauses_.push_back(BinaryClause(alit, curr_lit));
            }

			if (!seen[alit.var()] && (!(var(alit).decision_level == 0) || config_.track_implications())){
              if(!existsUnitClauseOf(alit.var())) {
                  if (var(alit).decision_level < DL)
                      tmp_clause.push_back(alit);
                  else
                      lits_at_current_dl++;
                  seen[alit.var()] = true;
              } else if(config_.track_implications()){
                // the unit clause is part of the implying clause set.
                links.parent_unit_clauses_.push_back(alit);
              }
			}
		}
	}
	if (!hasAntecedent(curr_lit)) {
		minimizeAndStoreUIPClause(curr_lit.neg(), tmp_clause, seen);
        uip_clause_implication_links_.push_back(links);
	}
//	if (var(curr_lit).decision_level > assertion_level_)
//		assertion_level_ = var(curr_lit).decision_level;
}

void Solver::printOnlineStats() {
	if (config_.quiet)
		return;

	cout << endl;
	cout << "time elapsed: " << stopwatch_.getElapsedSeconds() << "s" << endl;
	if(config_.verbose) {
	  cout << "conflict clauses (all / bin / unit) \t";
	  cout << num_conflict_clauses();
	  cout << "/" << statistics_.num_binary_conflict_clauses_ << "/"
	      << conflict_unit_clauses_.size() << endl;
	  cout << "failed literals found by implicit BCP \t "
	      << statistics_.num_failed_literals_detected_ << endl;
	  ;

	  cout << "implicit BCP miss rate \t "
	      << statistics_.implicitBCP_miss_rate() * 100 << "%";
	  cout << endl;

	  comp_manager_.gatherStatistics();

	  cout << "cache size " << statistics_.cache_MB_memory_usage()	<< "MB" << endl;
	  cout << "components (stored / hits) \t\t"
	      << statistics_.cached_component_count() << "/"
	      << statistics_.cache_hits() << endl;
	  cout << "avg. variable count (stored / hits) \t"
	      << statistics_.getAvgComponentSize() << "/"
	      << statistics_.getAvgCacheHitSize();
	  cout << endl;
	  cout << "cache miss rate " << statistics_.cache_miss_rate() * 100 << "%"
	      << endl;
	}
}



