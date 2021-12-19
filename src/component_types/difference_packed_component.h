/*
 * difference_packed_component.h
 *
 *  Created on: Feb 5, 2013
 *      Author: mthurley
 */

#ifndef DIFFERENCE_PACKED_COMPONENT_H_
#define DIFFERENCE_PACKED_COMPONENT_H_

#include "base_packed_component.h"
#include "component.h"

#include <math.h>



class DifferencePackedComponent:public BasePackedComponent {
public:

  DifferencePackedComponent() {
  }

  inline DifferencePackedComponent(Component &rComp){
    pack(rComp);
  }

  inline void pack(Component& comp);

  inline Component unpack(bool use_previous = false);

  unsigned num_variables() const{
    uint64_t *p = (uint64_t *) data_;
    return (*p >> bits_of_data_size()) & (uint64_t) variable_mask();

  }

  unsigned data_size() const {
         return *data_ & _data_size_mask;
    }

  unsigned data_only_byte_size() const {
        return data_size()* sizeof(unsigned);
    }

    unsigned raw_data_byte_size() const {
          return data_size()* sizeof(unsigned)
               + model_count_.get_mpz_t()->_mp_alloc * sizeof(mp_limb_t);
    }

    // raw data size with the overhead
    // for the supposed 16byte alignment of malloc
    unsigned sys_overhead_raw_data_byte_size() const {
      unsigned ds = data_size()* sizeof(unsigned);
      unsigned ms = model_count_.get_mpz_t()->_mp_alloc * sizeof(mp_limb_t);
//      unsigned mask = 0xfffffff8;
//      return (ds & mask) + ((ds & 7)?8:0)
//            +(ms & mask) + ((ms & 7)?8:0);
      unsigned mask = 0xfffffff0;
            return (ds & mask) + ((ds & 15)?16:0)
                  +(ms & mask) + ((ms & 15)?16:0);
    }

  bool equals(const DifferencePackedComponent &comp) const {
    if(hashkey_ != comp.hashkey())
      return false;
    unsigned* p = data_;
    unsigned* r = comp.data_;
    while(p != data_ + data_size()) {
        if(*(p++) != *(r++)){
            return false;
        }
    }
    return true;
  }

private:

};



void DifferencePackedComponent::pack(Component &rComp) {
  if(rComp.empty()){
    delete[] data_;
    data_ = nullptr;
    return;
  }

  unsigned max_var_diff = 0;
  unsigned hashkey_vars = *rComp.varsBegin();
  for (auto it = rComp.varsBegin() + 1; *it != varsSENTINEL; it++) {
    hashkey_vars = (hashkey_vars * 3) + *it;
    if ((*it - *(it - 1)) - 1 > max_var_diff)
      max_var_diff = (*it - *(it - 1)) - 1 ;
  }

  unsigned hashkey_clauses = *rComp.clsBegin();
  unsigned max_clause_diff = 0;
  if (*rComp.clsBegin()) {
    for (auto jt = rComp.clsBegin() + 1; *jt != clsSENTINEL; jt++) {
      hashkey_clauses = hashkey_clauses*3 + *jt;
      if (*jt - *(jt - 1) - 1 > max_clause_diff)
        max_clause_diff = *jt - *(jt - 1) - 1;
    }
  }

  hashkey_ = hashkey_vars + ((unsigned) hashkey_clauses << 11) + ((unsigned) hashkey_clauses >> 23);

  //VERIFIED the definition of bits_per_var_diff and bits_per_clause_diff
  unsigned bits_per_var_diff = log2(max_var_diff) + 1;
  unsigned bits_per_clause_diff = log2(max_clause_diff) + 1;

  assert(bits_per_var_diff <= 31);
  assert(bits_per_clause_diff <= 31);

  unsigned data_size_vars = bits_of_data_size() + 2*bits_per_variable() + 5;

  data_size_vars += (rComp.num_variables() - 1) * bits_per_var_diff ;

  unsigned data_size_clauses = bits_per_clause();
  if(*rComp.clsBegin())
    data_size_clauses += bits_per_clause() + 5
       + (rComp.numLongClauses() - 1) * bits_per_clause_diff;

  unsigned data_size = (data_size_vars + data_size_clauses)/bits_per_block();
    data_size+=  ((data_size_vars + data_size_clauses) % bits_per_block())? 1 : 0;

  // data_ will be cast to an uint_t* and dereferenced, so it must be large enough
  unsigned int minimum_data_size = sizeof(uint64_t) / sizeof(unsigned int);
  data_size = (data_size < minimum_data_size) ?  minimum_data_size : data_size;

  delete[] data_;
  data_ = new unsigned[data_size];

  assert((data_size >> bits_of_data_size()) == 0);
  BitStuffer<unsigned> bs(data_);

  bs.stuff(data_size, bits_of_data_size());
  bs.stuff(rComp.num_variables(), bits_per_variable());
  bs.stuff(bits_per_var_diff, 5);
  bs.stuff(*rComp.varsBegin(), bits_per_variable());

  if(bits_per_var_diff)
  for (auto it = rComp.varsBegin() + 1; *it != varsSENTINEL; it++)
    bs.stuff(*it - *(it - 1) - 1, bits_per_var_diff);

  // storing the number of clauses is redundant, but safer than trying to infer it from the data size
  bs.stuff(rComp.numLongClauses(), bits_per_clause());

  if (*rComp.clsBegin()) {
    bs.stuff(bits_per_clause_diff, 5);
    bs.stuff(*rComp.clsBegin(), bits_per_clause());
    if(bits_per_clause_diff)
     for (auto jt = rComp.clsBegin() + 1; *jt != clsSENTINEL; jt++)
      bs.stuff(*jt - *(jt - 1) - 1, bits_per_clause_diff);
  }

  // to check wheter the "END" block of bits_per_clause()
  // many zeros fits into the current
  //bs.end_check(bits_per_clause());
  // this will tell us if we computed the data_size
  // correctly
  //TODO no longer correct due to minimum_data_size
  //bs.assert_size(data_size);
}


//DifferencePackedComponent::DifferencePackedComponent(Component &rComp) {
//
//  unsigned max_var_diff = 0;
//  unsigned hashkey_vars = *rComp.varsBegin();
//  for (auto it = rComp.varsBegin() + 1; *it != varsSENTINEL; it++) {
//    hashkey_vars = (hashkey_vars * 3) + *it;
//    if ((*it - *(it - 1)) > max_var_diff)
//      max_var_diff = (*it - *(it - 1)) ;
//  }
//
//  unsigned hashkey_clauses = *rComp.clsBegin();
//  unsigned max_clause_diff = 0;
//  if (*rComp.clsBegin()) {
//    for (auto jt = rComp.clsBegin() + 1; *jt != clsSENTINEL; jt++) {
//      hashkey_clauses = hashkey_clauses * 3 + *jt;
//      if (*jt - *(jt - 1) > max_clause_diff)
//        max_clause_diff = *jt - *(jt - 1);
//    }
//  }
//
//  hashkey_ = hashkey_vars + (((unsigned) hashkey_clauses) << 16);
//
//  //VERIFIED the definition of bits_per_var_diff and bits_per_clause_diff
//  unsigned bits_per_var_diff = log2(max_var_diff) + 1;
//  unsigned bits_per_clause_diff = log2(max_clause_diff) + 1;
//
//  unsigned data_size_vars = 2*bits_per_variable() + 5;
//
//  data_size_vars += (rComp.num_variables() - 1) * bits_per_var_diff ;
//
//  unsigned data_size_clauses = bits_per_clause();
//  if(*rComp.clsBegin())
//    data_size_clauses += bits_per_clause() + 5
//       + (rComp.numLongClauses() - 1) * bits_per_clause_diff;
//
//  unsigned data_size = (data_size_vars + data_size_clauses)/bits_per_block();
//    data_size+=  ((data_size_vars + data_size_clauses) % bits_per_block())? 1 : 0;
//
//  data_ = new unsigned[data_size];
//
//  BitStuffer<unsigned> bs(data_);
//
//  bs.stuff(rComp.num_variables(), bits_per_variable());
//  bs.stuff(bits_per_var_diff, 5);
//  bs.stuff(*rComp.varsBegin(), bits_per_variable());
//
//  for (auto it = rComp.varsBegin() + 1; *it != varsSENTINEL; it++)
//    bs.stuff(*it - *(it - 1), bits_per_var_diff);
//
//  if (*rComp.clsBegin()) {
//    bs.stuff(bits_per_clause_diff, 5);
//    bs.stuff(*rComp.clsBegin(), bits_per_clause());
//    for (auto jt = rComp.clsBegin() + 1; *jt != clsSENTINEL; jt++)
//      bs.stuff(*jt - *(jt - 1), bits_per_clause_diff);
//  }
//
//  // to check wheter the "END" block of bits_per_clause()
//  // many zeros fits into the current
//  bs.end_check(bits_per_clause());
//  // this will tell us if we computed the data_size
//  // correctly
//  bs.assert_size(data_size);
//}

Component DifferencePackedComponent::unpack(bool use_previous) {
    Component result;

    // dummy Element?
    if(!data_){
      return result;
    }

    BitUnstuffer<unsigned int> unstuffer(data_);
    unsigned int data_size = unstuffer.unstuff(bits_of_data_size(use_previous));

    unsigned int num_of_variables = unstuffer.unstuff(bits_per_variable(use_previous));
    unsigned int bits_per_var_diff = unstuffer.unstuff(5);

    // the first variable is stored directly
    unsigned int current_variable = unstuffer.unstuff(bits_per_variable(use_previous));
    // current_variable might be the sentinel if the component is empty
    if(num_of_variables){
      result.addVar(current_variable);
    }

    // the remaining variables are only stored by their difference to their predecessor
    for(unsigned int i = 1; i < num_of_variables; i++){
      current_variable += unstuffer.unstuff(bits_per_var_diff) + 1;
      result.addVar(current_variable);
    }

    result.closeVariableData();

    unsigned int num_of_clauses = unstuffer.unstuff(bits_per_clause(use_previous));

    if(num_of_clauses){
      unsigned int bits_per_clause_diff = unstuffer.unstuff(5);

      // the first clause is stored directly
      unsigned int current_clause = unstuffer.unstuff(bits_per_clause(use_previous));
      if(num_of_clauses){
        result.addCl(current_clause);
      }

      // the remaining clauses are only stored by their difference to their predecessor
      for(unsigned int i = 1; i < num_of_clauses; i++){
        current_clause += unstuffer.unstuff(bits_per_clause_diff) + 1;
        result.addCl(current_clause);
      }

    }

    result.closeClauseData();

    return result;
}



#endif /* DIFFERENCE_PACKED_COMPONENT_H_ */
