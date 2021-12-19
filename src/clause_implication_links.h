#ifndef CLAUSE_IMPILCATION_LINKS_H_
#define CLAUSE_IMPILCATION_LINKS_H_

#include "structures.h"

struct ClauseImplicationLinks{
  vector<ClauseOfs> parent_long_clauses_;
  vector<BinaryClause> parent_binary_clauses_;
  vector<LiteralID> parent_unit_clauses_;

  vector<ClauseOfs> child_long_clauses_;
  vector<BinaryClause> child_binary_clauses_;
  vector<LiteralID> child_unit_clauses_;
};

#endif // CLAUSE_IMPILCATION_LINKS_H_
