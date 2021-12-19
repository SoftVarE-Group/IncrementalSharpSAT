#include "solver.h"

#include <iostream>
#include <fstream>

#include <vector>

//#include <malloc.h>
#include <string>

#include <sys/time.h>
#include <sys/resource.h>

using namespace std;


int main(int argc, char *argv[]) {

  string file_name;
  SolverConfiguration config;


  if (argc == 2 && (strcmp(argv[1], "-h") == 0 || strcmp(argv[1], "--help") == 0)) {
    cout << "Usage: " << argv[0] << " [options] [CNF_File]" << endl;
    cout << "Options: " << endl;
    cout << "\t --help \t show this screen" << endl;
    cout << "\t -stdin \t take inputs from stdin after CNF_File has been fully processed" << endl;
    cout << "\t -r     \t allow clause removal" << endl;
    cout << "\t -noPP  \t turn off preprocessing" << endl;
    cout << "\t -q     \t quiet mode" << endl;
    cout << "\t -v     \t verbose mode" << endl;
    cout << "\t -t [s] \t set time bound to s seconds" << endl;
    cout << "\t -noCC  \t turn off component caching" << endl;
    cout << "\t -cs [n]\t set max cache size to n MB" << endl;
    cout << "\t -noIBCP\t turn off implicit BCP" << endl;
    cout << "\t -noSR  \t turn off score reuse" << endl;
    cout << "\t -noClR \t turn off clause reuse" << endl;
    cout << "\t -noCoR \t turn off component cache reuse" << endl;
    cout << "\t -c [a] \t set cache cleanup agressiveness to a. Maximum is 2" << endl;
    cout << "\t -d [i] \t adjusts decision variable selection to added clauses with cost dependent on i. Maximum is 2" << endl;
    cout << "\t" << endl;

    return -1;
  }

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "-r") == 0)
      config.allow_clause_removal = true;
    else if (strcmp(argv[i], "-noCC") == 0)
      config.perform_component_caching = false;
    else if (strcmp(argv[i], "-noIBCP") == 0)
      config.perform_failed_lit_test = false;
    else if (strcmp(argv[i], "-noPP") == 0)
      config.perform_pre_processing = false;
    else if (strcmp(argv[i], "-noSR") == 0)
      config.reuse_literal_scores = false;
    else if (strcmp(argv[i], "-noClR") == 0)
      config.reuse_learned_clauses = false;
    else if (strcmp(argv[i], "-noCoR") == 0)
      config.reuse_component_cache = false;
    else if (strcmp(argv[i], "-c") == 0){
      if (argc <= i + 1) {
        cout << " wrong parameters" << endl;
        return -1;
      }
      config.cache_cleanup_agressiveness = atoi(argv[++i]);
    }
    else if (strcmp(argv[i], "-d") == 0){
      if (argc <= i + 1) {
        cout << " wrong parameters" << endl;
        return -1;
      }
      config.variable_selection_adjustment = atoi(argv[++i]);
    }
    else if (strcmp(argv[i], "-stdin") == 0)
      config.fallbackToStdin = true;
    else if (strcmp(argv[i], "-q") == 0)
      config.quiet = true;
    else if (strcmp(argv[i], "-v") == 0)
      config.verbose = true;
    else if (strcmp(argv[i], "-t") == 0) {
      if (argc <= i + 1) {
        cout << " wrong parameters" << endl;
        return -1;
      }
      config.time_bound_seconds = atol(argv[++i]);
      if (config.verbose)
        cout << "time bound set to" << config.time_bound_seconds << "s\n";
     } else if (strcmp(argv[i], "-cs") == 0) {
      if (argc <= i + 1) {
        cout << " wrong parameters" << endl;
        return -1;
      }
      config.maximum_cache_size_bytes_ = atol(argv[++i]) * (uint64_t) 1000000;
    } else{
      config.startWithStdin = false;
      file_name = argv[i];
    }
  }

  // selects and opens the stream containing the input
  istream* input_file;
  if(config.startWithStdin){
    input_file = &cin;
  }
  else{
    input_file = new ifstream(file_name);
    if (!(*input_file)) {
      cerr << "Cannot open file: " << file_name << endl;
      exit(0);
    }
  }

  Solver theSolver(config);

  // solve loop: feeds the solver formulas until it runs out of file
  bool currently_uses_stdin  = config.startWithStdin;
  while(true){
    // checks for end of input file
    if(input_file->peek() == EOF){
      if(currently_uses_stdin){
        // no more replacement options
        break;
      }
      else{
        // file is not stdin, so it needs to be closed and deleted
        ((ifstream*)input_file)->close();
        delete input_file;

        // does input_file need to be replaced with stdin?
        if(config.fallbackToStdin){
          input_file = &cin;
          currently_uses_stdin = true;

          // we need to check for EOF again in case there is no user input
          continue;
        }
        else{
          break;
        }
      }
    }

    // load and solve
    theSolver.createfromFile(*input_file);
    theSolver.solve();
  }

//  cout << sizeof(LiteralID)<<"MALLOC_STATS:" << endl;
//  malloc_stats();

//  rusage ru;
//  getrusage(RUSAGE_SELF,&ru);
//
//   cout << "\nRus: " <<  ru.ru_maxrss*1024 << endl;
//  cout << "\nMALLINFO:" << endl;
//
//  cout << "total " << mallinfo().arena + mallinfo().hblkhd << endl;
//  cout <<  mallinfo().arena << "non-mmapped space allocated from system " << endl;
//  cout <<  mallinfo().ordblks << "number of free chunks " << endl;
//  cout <<  mallinfo().smblks<< "number of fastbin blocks " << endl;
//  cout <<  mallinfo().hblks<< " number of mmapped regions " << endl;
//  cout <<  mallinfo().hblkhd<< "space in mmapped regions " << endl;
//  cout <<  mallinfo().usmblks<< " maximum total allocated space " << endl;
//  cout <<  mallinfo().fsmblks<< "space available in freed fastbin blocks " << endl;
//  cout <<  mallinfo().uordblks<< " total allocated space " << endl;
//  cout <<  mallinfo().fordblks<< "total free space " << endl;
//  cout <<  mallinfo().keepcost<< " top-most, releasable (via malloc_trim) space " << endl;
  return 0;
}
