/*
 * structures.h
 *
 *  Created on: Jun 25, 2012
 *      Author: Marc Thurley
 */

#ifndef STRUCTURES_H_
#define STRUCTURES_H_

#include <vector>
#include <iostream>
#include "primitive_types.h"
using namespace std;



#define INVALID_DL -1

typedef unsigned char TriValue;
#define   F_TRI  0
#define   T_TRI  1
#define   X_TRI  2

class LiteralID {
public:

  LiteralID() {
    value_ = 0;
  }
  LiteralID(int lit) {
    value_ = (abs(lit) << 1) + (unsigned) (lit > 0);
  }

  LiteralID(VariableIndex var, bool sign) {
    value_ = (var << 1) + (unsigned) sign;
  }

  VariableIndex var() const {
    return (value_ >> 1);
  }

  int toInt() const {
    return ((int) value_ >> 1) * ((sign()) ? 1 : -1);
  }

  void inc(){++value_;}

  void copyRaw(unsigned int v) {
    value_ = v;
  }

  bool sign() const {
    return (bool) (value_ & 0x01);
  }

  bool operator!=(const LiteralID &rL2) const {
    return value_ != rL2.value_;
  }

  bool operator==(const LiteralID &rL2) const {
    return value_ == rL2.value_;
  }

  const LiteralID neg() const {
    return LiteralID(var(), !sign());
  }

  void print() const {
    cout << (sign() ? " " : "-") << var() << " ";
  }

  unsigned raw() const { return value_;}

private:
  unsigned value_;

  template <class _T> friend class LiteralIndexedVector;
};

static const LiteralID NOT_A_LIT(0, false);
#define SENTINEL_LIT NOT_A_LIT

class Literal {
public:
  vector<LiteralID> original_binary_links_ = vector<LiteralID>(1,SENTINEL_LIT);
  vector<LiteralID> conflict_binary_links_ = vector<LiteralID>(1,SENTINEL_LIT);
  vector<ClauseOfs> watch_list_ = vector<ClauseOfs>(1,SENTINEL_CL);

  // separates score for prevalence in clauses from score for activity during solving.
  // this allows us to adjust for changes to the formula without resettting the activity
  float prevalence_score_ = 0.0f;
  float activity_score_ = 0.0f;

  void increasePrevalence(unsigned int u = 1){
    prevalence_score_ += u;
  }

  void decreasePrevalence(unsigned int u = 1){
    prevalence_score_ -= u;
  }

  void increaseActivity(unsigned u = 1){
    activity_score_+= u;
  }

  float totalScore(){
    return prevalence_score_ + activity_score_;
  }

  void removeWatchLinkTo(ClauseOfs clause_ofs) {
    for (auto it = watch_list_.begin(); it != watch_list_.end(); it++)
          if (*it == clause_ofs) {
            *it = watch_list_.back();
            watch_list_.pop_back();
            return;
          }
  }

  void replaceWatchLinkTo(ClauseOfs clause_ofs, ClauseOfs replace_ofs) {
        for (auto it = watch_list_.begin(); it != watch_list_.end(); it++)
          if (*it == clause_ofs) {
            *it = replace_ofs;
            return;
          }
  }

  void addWatchLinkTo(ClauseIndex clause_ofs) {
    watch_list_.push_back(clause_ofs);
  }

  void addBinLinkTo(LiteralID lit, bool conflict) {
    // selecting the appropriate list of links
    vector<LiteralID>& binary_links_ = conflict ? conflict_binary_links_ : original_binary_links_;

    binary_links_.back() = lit;
    binary_links_.push_back(SENTINEL_LIT);
  }

  void resetWatchList(){
        watch_list_.clear();
        watch_list_.push_back(SENTINEL_CL);
  }

  bool hasBinaryLinkTo(LiteralID lit) {
    for (auto l : original_binary_links_) {
      if (l == lit)
        return true;
    }
    for (auto l : conflict_binary_links_ ) {
      if (l == lit)
        return true;
    }
    return false;
  }

  bool hasBinaryLinks() {
    return (!original_binary_links_.empty()) || (!conflict_binary_links_.empty());
  }
};

template<>
struct std::hash<LiteralID>{
  size_t operator()(const LiteralID& to_hash) const{
    return hash<unsigned>()(to_hash.raw());
  }
};

class Antecedent {
  unsigned int val_;

public:
  Antecedent() {
    val_ = 1;
  }

  Antecedent(const ClauseOfs cl_ofs) {
     val_ = (cl_ofs << 1) | 1;
   }
  Antecedent(const LiteralID idLit) {
    val_ = (idLit.raw() << 1);
  }

  bool isAClause() const {
    return val_ & 0x01;
  }

  ClauseOfs asCl() const {
      return val_ >> 1;
    }

  LiteralID asLit() {
    LiteralID idLit;
    idLit.copyRaw(val_ >> 1);
    return idLit;
  }
  // A NON-Antecedent will only be A NOT_A_CLAUSE Clause Id
  bool isAnt() {
    return val_ != 1; //i.e. NOT a NOT_A_CLAUSE;
  }
};


struct Variable {
  Antecedent ante;
  int decision_level = INVALID_DL;
};

// for now Clause Header is just a dummy
// we keep it for possible later changes
class ClauseHeader {
  unsigned creation_time_; // number of conflicts seen at creation time
  unsigned score_;
  unsigned length_;
public:

  void increaseScore() {
    score_++;
  }
  void decayScore() {
      score_ >>= 1;
  }
  unsigned score() {
      return score_;
  }

  unsigned creation_time() {
      return creation_time_;
  }
  unsigned length(){ return length_;}
  void set_length(unsigned length){ length_ = length;}

  void set_creation_time(unsigned time) {
    creation_time_ = time;
  }
  static unsigned overheadInLits(){return sizeof(ClauseHeader)/sizeof(LiteralID);}
};

// pair of LiteralIDs which does not care about the order
struct BinaryClause{
  LiteralID first, second;

  BinaryClause(LiteralID first, LiteralID second){
    this->first= first;
    this->second = second;
  }

  bool operator==(const BinaryClause& other) const{
    return (first == other.first && second == other.second) || (first == other.second && second == other.first);
  }
};

template<>
struct std::hash<BinaryClause>{
  size_t operator()(const BinaryClause& to_hash) const{
    return hash<LiteralID>()(to_hash.first) ^ hash<LiteralID>()(to_hash.second);
  }
};

#endif /* STRUCTURES_H_ */
