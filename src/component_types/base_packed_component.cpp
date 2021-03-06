/*
 * base_packed_component.cpp
 *
 *  Created on: Feb 4, 2013
 *      Author: mthurley
 */
#include "base_packed_component.h"
#include <math.h>
#include <iostream>

unsigned BasePackedComponent::_bits_per_clause = 0;
unsigned BasePackedComponent::_bits_per_variable = 0; // bitsperentry
unsigned BasePackedComponent::_variable_mask = 0;
unsigned BasePackedComponent::_clause_mask = 0; // bitsperentry
unsigned BasePackedComponent::_debug_static_val=0;
unsigned BasePackedComponent::_bits_of_data_size=0;
unsigned BasePackedComponent::_data_size_mask = 0;

unsigned int BasePackedComponent::_previous_bits_of_data_size = 0;
unsigned int BasePackedComponent::_previous_bits_per_clause = 0;
unsigned int BasePackedComponent::_previous_bits_per_variable = 0;

bool BasePackedComponent::testPackSizeAdjustment(unsigned int maxVarId, unsigned int maxClId){
  if(_bits_per_variable != log2(maxVarId) + 1){
    return true;
  } else if(_bits_per_clause != log2(maxClId) + 1){
    return true;
  } else if(_bits_of_data_size != log2(maxVarId + maxClId) + 1){
    return true;
  } else{
    return false;
  }
}


void BasePackedComponent::adjustPackSize(unsigned int maxVarId,
    unsigned int maxClId) {
  // stores previous sizes for resizing the existing cache entries
  _previous_bits_of_data_size = _bits_of_data_size;
  _previous_bits_per_clause = _bits_per_clause;
  _previous_bits_per_variable = _bits_per_variable;

  _bits_per_variable = log2(maxVarId) + 1;
  _bits_per_clause = log2(maxClId) + 1;

  _bits_of_data_size = log2(maxVarId + maxClId) + 1;

  _variable_mask = _clause_mask = _data_size_mask = 0;
  for (unsigned int i = 0; i < _bits_per_variable; i++)
    _variable_mask = (_variable_mask << 1) + 1;
  for (unsigned int i = 0; i < _bits_per_clause; i++)
    _clause_mask = (_clause_mask << 1) + 1;
  for (unsigned int i = 0; i < _bits_of_data_size; i++)
    _data_size_mask = (_data_size_mask << 1) + 1;
}




