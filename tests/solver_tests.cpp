#include <fstream>

#include <gtest/gtest.h>

#include "../src/solver.h"

class SolverTests : public testing::TestWithParam<tuple<bool, bool, bool, int, int, bool>> {
  protected:
    void SetUp(){
      config.quiet = true;

      config.reuse_literal_scores = get<0>(GetParam());
      config.reuse_component_cache = get<1>(GetParam());
      config.reuse_learned_clauses = get<2>(GetParam());
      config.cache_cleanup_agressiveness = get<3>(GetParam());
      config.variable_selection_adjustment = get<4>(GetParam());
      config.adaptive_cache_limit = get<5>(GetParam());

      // the optimizations are only sensible if the cache is reused
      if(!config.reuse_component_cache && (config.cache_cleanup_agressiveness || config.variable_selection_adjustment)){
        GTEST_SKIP();
      }
    }

    // prepares for the calls of solve_next_query
    void prepare(string file_name, bool allow_removal = false){
      // we only allow clause removal if the testcase needs it
      config.allow_clause_removal = allow_removal;
      solver = new Solver(config);

      file = ifstream(file_name);
      if (!file) {
        cerr << "Cannot open file: " << file_name << endl;
        exit(0);
      }
    }

    void solve_next_query(){
      solver->createfromFile(file);
      solver->solve();
    }

    void Teardown(){
      if(solver){
        delete solver;
      }
    }

    ifstream file;

    Solver *solver;
    SolverConfiguration config;
};

// the lambda expression at the end translates the config tuple to a human-readable form
INSTANTIATE_TEST_SUITE_P(MultipleConfigs, SolverTests, testing::Combine(testing::Bool(), testing::Bool(), testing::Bool(), testing::Range(0, 3), testing::Range(0, 3), testing::Bool()),
                        [](const testing::TestParamInfo<SolverTests::ParamType>& config){
                            string result;

                            // score reuse
                            if(!get<0>(config.param)){
                              result += "NoScores";
                            }
                            // component reuse
                            if(!get<1>(config.param)){
                              result += "NoComponents";
                            }
                            // clause reuse
                            if(!get<2>(config.param)){
                              result += "NoClauses";
                            }

                            // cache cleanup agression
                            if(get<3>(config.param)){
                              result += "Cleanup" + to_string(get<3>(config.param));
                            }
                            // adjustment to decision variable selection
                            if(get<4>(config.param)){
                              result += "AdjSelection" + to_string(get<4>(config.param));
                            }
                            // adaptive cache maximum
                            if(get<5>(config.param)){
                              result += "AdaptiveMax";
                            }

                            // gtest does not want this string to be empty
                            if(result.empty()){
                              result += "BaseConfig";
                            }

                            return result;
                        });

TEST_P(SolverTests, DuplicateLiteralInClause){
  prepare("../tests/resources/duplicate_literal");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 3);
}

TEST_P(SolverTests, TautologicalClause){
  prepare("../tests/resources/taut_clause");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 5);
}

TEST_P(SolverTests, DuplicateLiteralInTautologicalClause){
  prepare("../tests/resources/duplicate_literal_in_taut_clause");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 12);
}

TEST_P(SolverTests, OneAssumptionSmall){
  prepare("../tests/resources/one_clause");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 15);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 7);

  // runs again without assumptions to catch lingering effects of assumptions
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), 15);
}


TEST_P(SolverTests, OneAssumptionLargeish){
  // with the normal factor, the adaptive limit is too low for this formula. This is not a bug, but a conceptual problem
  config.adaptive_cache_limit_factor_ = 1000;

  prepare("../tests/resources/xor_tree_7");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("7237005577332262213973186563042994240829374041602535252466099000494570602496"));

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("3618502788666131106986593281521497120414687020801267626233049500247285301248"));

  // runs again without assumptions to catch lingering effects of assumptions
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("7237005577332262213973186563042994240829374041602535252466099000494570602496"));
}

// very slow
TEST_P(SolverTests, DISABLED_OneAssumptionLarge){
  // with the normal factor, the adaptive limit is too low for this formula. This is not a bug, but a conceptual problem
  config.adaptive_cache_limit_factor_ = 40000;

  prepare("../tests/resources/xor_tree_8");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("837987995621412318723376562387865382967460363787024586107722590232610251879596686050117143635431464230626991136655378178359617675746660621652103062880256"));

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("418993997810706159361688281193932691483730181893512293053861295116305125939798343025058571817715732115313495568327689089179808837873330310826051531440128"));

  // runs again without assumptions to catch lingering effects of assumptions
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("837987995621412318723376562387865382967460363787024586107722590232610251879596686050117143635431464230626991136655378178359617675746660621652103062880256"));
}

TEST_P(SolverTests, StartsWithOneAssumptionSmall){
  prepare("../tests/resources/simple_implication");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 3);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 5);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 4);
}

TEST_P(SolverTests, StartsWithOneAssumptionLarge){
  prepare("../tests/resources/php_5");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 6);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 30);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 18);
}

TEST_P(SolverTests, MultipleAssumptions){
  prepare("../tests/resources/square_grid_4");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 128);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 4);

  // changing assignment directly instead of solving empty in between
  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 16);
}

TEST_P(SolverTests, DamageableByProprocessing){
  prepare("../tests/resources/damageable_by_preprocessing");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 4);

  // runs again in case damage only has effect on second run
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), 4);
}

TEST_P(SolverTests, AddClausesIndividuallySmall){
  prepare("../tests/resources/overlapping_ternary");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 12);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 9);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 8);

  // repeating final run in case errors only occur later
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), 8);
}

TEST_P(SolverTests, AddClausesIndividuallyLarge){
  prepare("../tests/resources/exp_3");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 384);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 256);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 128);

  // repeating final run in case errors only occur later
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), 128);
}

TEST_P(SolverTests, AddMultipleClausesAtOnce){
  prepare("../tests/resources/fact");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 12);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 9);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 4);

  // repeating final run in case errors only occur later
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), 4);
}

TEST_P(SolverTests, AddClauseIndividuallyThenMultipleClausesAtOnce){
  prepare("../tests/resources/const_grid_64");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("12979374126081769472"));

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("9799832789158199296"));
;
  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("2305843009213693952"));

  // repeating final run in case errors only occur later
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("2305843009213693952"));
}

TEST_P(SolverTests, IncreaseVariableNumber){
  prepare("../tests/resources/pyramid_10");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("4710128697246244834921603689"));

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("7568884996961026390511932621814249313300473895700507076910655578449314614828101548376064"));

  // repeating final run in case errors only occur later
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("7568884996961026390511932621814249313300473895700507076910655578449314614828101548376064"));
}

TEST_P(SolverTests, AddClauseIndividuallyAndIncreaseVariableNumber){
  prepare("../tests/resources/line_128");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("85070591730234615865843651857942052864"));

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("1276058875953519237987654777869130792960"));

  // repeating final run in case errors only occur later
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("1276058875953519237987654777869130792960"));
}


TEST_P(SolverTests, MultipleAssumptionsAndAddMultipleClausesAtOnce){
  prepare("../tests/resources/log_road_5");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("4194304"));

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("131072"));

  // runs again without assumptions to catch lingering effects of assumptions
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("1179648"));
}

TEST_P(SolverTests, ContradictoryUnitClauses){
  // this test fails in the orignal solver
  prepare("../tests/resources/contradictory_unit_clauses");

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), 0);
}

TEST_P(SolverTests, RemoveClausesIndividually){
  prepare("../tests/resources/berkeleydb.dimacs", true);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("4080389785"));

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("5440512409"));

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("6800656946"));

  // runs again to test if removal is permanent
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("6800656946"));
}

TEST_P(SolverTests, RemoveMultipleClausesAtOnce){
  prepare("../tests/resources/financialServices.dimacs", true);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("97451212554676"));

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("22846775988609240994"));

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("26083083754338384756"));

  // runs again to test if removal is permanent
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("26083083754338384756"));
}

TEST_P(SolverTests, RemoveUnitClauses){
  prepare("../tests/resources/min_space_1024", true);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("1396"));

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("13060"));

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("9638280"));

  // runs again to test if removal is permanent
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("9638280"));
}

TEST_P(SolverTests, AddAndRemoveClauses){
  prepare("../tests/resources/embtoolkit.dimacs", true);

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("5134555717728405373874099868199035516442186387628134162059302739740605826105226151439263334400000"));

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("2246368126506177351069918692337078038443456544587308695900942593120184286352313257908240384000000"));

  solve_next_query();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("2019571344503084230425662315728822918016688527386588487726698620858192102551682584148757708800000"));

  // runs again to test if removal is permanent
  solver->solve();
  EXPECT_EQ(solver->statistics().final_solution_count(), mpz_class("2019571344503084230425662315728822918016688527386588487726698620858192102551682584148757708800000"));
}
