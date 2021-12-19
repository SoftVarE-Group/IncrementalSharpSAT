/*
 * basic_types.h
 *
 *  Created on: Jun 24, 2012
 *      Author: Marc Thurley
 */

#ifndef SOLVER_CONFIG_H_
#define SOLVER_CONFIG_H_


struct SolverConfiguration {

  bool perform_non_chron_back_track = true;

  // TODO component caching cannot be deactivated for now!
  bool perform_component_caching = true;
  bool perform_failed_lit_test = true;
  //TODO deactivationg preprocessing can currently lead to crashes
  bool perform_pre_processing = true;

  bool reuse_component_cache = true;
  bool reuse_learned_clauses = true;
  bool reuse_literal_scores = true;

  unsigned int cache_cleanup_agressiveness = 0;
  unsigned int variable_selection_adjustment = 0;

  bool allow_clause_removal = false;

  unsigned long time_bound_seconds = 100000;

  // determines if and when to use stdin for the formula input
  bool startWithStdin = true;
  bool fallbackToStdin = false;

  bool verbose = false;

  // quiet = true will override verbose;
  bool quiet = false;

  // if adaptive_cache_limit_ is true, the solver will set the maximum cache size to adaptive_cache_limit_factor_ times the cache size after the next query
  bool adaptive_cache_limit = false;
  float adaptive_cache_limit_factor_ = 2;

  uint64_t maximum_cache_size_bytes_ = 0;

  // if we reuse the learned clauses and allow removal, we need to track what implied the learned clauses so we can remove them if tehy become invalid
  bool track_implications(){
    return reuse_learned_clauses && allow_clause_removal;
  }
};

#endif /* SOLVER_CONFIG_H_ */
