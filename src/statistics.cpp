/*
 * statistics.cpp
 *
 *  Created on: Feb 13, 2013
 *      Author: mthurley
 */

#include "statistics.h"

#include <iostream>
#include <fstream>

using namespace std;

void DataAndStatistics::print_final_solution_count() {
  cout << final_solution_count_.get_str();
}

void DataAndStatistics::writeToFile(const string & file_name) {
  ofstream out(file_name, ios_base::app);
  unsigned pos = input_file_.find_last_of("/\\");
  out << "<tr>" << endl;
  out << "<td>" << input_file_.substr(pos + 1) << "</td>" << endl;
  out << "<td>" << num_original_variables_ << "</td>" << endl;
  out << "<td>" << num_original_clauses_ << "</td>" << endl;
  out << "<td>" << num_total_decisions_ - num_decisions_at_start_ << "</td>" << endl;
  out << "<td>" << time_elapsed_ << "</td>" << endl;

  string s = final_solution_count_.get_str();
  if (final_solution_count_ == 0)
    s = "UNSAT";
  out << "<td>" << s << "</td>" << endl;
  out << "</tr>" << endl;
}

void DataAndStatistics::printShort() {
  if (exit_state_ == TIMEOUT) {
    cout << endl << " TIMEOUT !" << endl;
    return;
  }
  cout << endl << endl;
  cout << "variables\t\t\t\t" << num_variables_ << endl;
  cout << "clauses (removed) \t\t\t" << num_original_clauses_ << " ("
      << num_original_clauses_ - num_clauses() << ")" << endl;
  cout << "decisions \t\t\t\t" << num_total_decisions_ - num_decisions_at_start_ << endl;
  cout << "conflicts \t\t\t\t" << num_total_conflicts_ - num_conflicts_at_start_ << endl;
  cout << "conflict clauses (all/bin/unit) \t";
  cout << num_conflict_clauses();
  cout << "/" << num_binary_conflict_clauses_ << "/" << num_conflict_unit_clauses_
      << endl << endl;

  cout << "preparation time \t\t\t" << time_for_preparations_ << "s" << endl;
  cout << "reused clauses (all/bin/unit) \t\t";
  cout << num_reused_clauses();
  cout << "/" << num_reused_binary_clauses_ << "/" << num_reused_unit_clauses_ << endl;
  cout << "reused cache entries \t\t\t" << num_reused_components_ << endl << endl;

  cout << "failed literals found by implicit BCP \t"
      << num_failed_literals_detected_ << endl;
  cout << "implicit BCP miss rate \t\t\t" << implicitBCP_miss_rate() * 100 << "%";
  cout << endl;
  cout << "bytes cache size     \t\t\t" << cache_bytes_memory_usage()  << "\t"
      << endl;

  cout << "bytes cache (overall) \t\t\t" << overall_cache_bytes_memory_stored()
      << "" << endl;
  cout << "bytes cache (infra / comps) \t\t"
      << (cache_infrastructure_bytes_memory_usage_) << "/"
      << sum_bytes_cached_components_  << "\t" << endl;

  cout << "bytes pure comp data (curr) \t\t" << sum_bytes_pure_cached_component_data_  << "" << endl;
  cout << "bytes pure comp data (overall) \t\t" <<overall_bytes_pure_stored_component_data_ << "" << endl;

  cout << "bytes cache with sysoverh (curr) \t" << sys_overhead_sum_bytes_cached_components_  << "" << endl;
  cout << "bytes cache with sysoverh (overall) \t" << sys_overhead_overall_bytes_components_stored_ << "" << endl;


  cout << "cache (stores / hits) \t\t\t" << num_cached_components_ << "/"
      << num_cache_hits_ << endl;
  cout << "cache miss rate \t\t\t" << cache_miss_rate() * 100 << "%" << endl;
  cout << "avg. variable count (stores / hits) \t" << getAvgComponentSize()
      << "/" << getAvgCacheHitSize() << endl << endl;
  cout << "\n# solutions " << endl;

  print_final_solution_count();

  cout << "\n# END" << endl << endl;
  cout << "time: " << time_elapsed_ << "s\n\n";
}
