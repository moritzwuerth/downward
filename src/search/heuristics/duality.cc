//
// Created by moritz on 23.08.22.
//

#include "duality.h"
#include "../option_parser.h"
#include "../plugin.h"
#include <vector>
#include "cassert"

using namespace std;

namespace dual {

    // construction and destruction
    Duality::Duality(const options::Options &opts)
            : Heuristic(opts) {

        //build strips_task
        stripsTask = strips_task::Normal_Stripstask(task_proxy);
        dual_StripsTask = strips_task::Dual_StripsTask(stripsTask);
        setup_initial_state();

        relaxed_exploration();


    }
    void Duality::setup_initial_state() {

        for (PropID &propId : dual_StripsTask.initial_propositions){
            dual_StripsTask.h_value_for_single_propId[propId] = 0;

            for (PropID &propId2 : dual_StripsTask.initial_propositions) {
                if (propId < propId2) {
                    dual_StripsTask.h_value_for_pair[propId][propId2] = 0;
                }
            }
        }
    }
//TODO rekursiv, dass will ich noch machen
    void Duality::relaxed_exploration() {
        bool changed = true;
        while (changed) {
            changed = false;
            //sets value for individual variables
            for (int i = 0; i < dual_StripsTask.h_value_for_single_propId.size(); ++i) {

                //goes through all operators
                for (UnaryOperator &unaryOperator: dual_StripsTask.unary_operators) {

                    //checks if delete effect is present
                    if (std::find(unaryOperator.del_effects.begin(), unaryOperator.del_effects.end(),
                                  i) != unaryOperator.del_effects.end()) {

                    } else {

                        if (std::find(unaryOperator.add_effect.begin(), unaryOperator.add_effect.end(), i) !=
                            unaryOperator.add_effect.end()) {


                            vector <PropID> resulte_after_operator{i};


                            //operator is used (regression)
                            for (PropID propId : unaryOperator.add_effect){
                                resulte_after_operator.erase(std::remove(resulte_after_operator.begin(), resulte_after_operator.end(), propId),
                                           resulte_after_operator.end());
                            }

                            resulte_after_operator.reserve((unaryOperator.preconditions.size()));
                            resulte_after_operator.insert(resulte_after_operator.end(), unaryOperator.preconditions.begin(),
                                        unaryOperator.preconditions.end());
                            utils::sort_unique(resulte_after_operator);

                            //takes min with temp.size() <= 2. with more it takes max
                            int cost = 0;
                            if (resulte_after_operator.size() == 1) {
                                cost = dual_StripsTask.h_value_for_single_propId[resulte_after_operator[0]];
                            } else if (resulte_after_operator.size() == 2) {
                                cost = dual_StripsTask.h_value_for_pair[resulte_after_operator[0]][resulte_after_operator[1]];
                            } else if (resulte_after_operator.size() < 1) {
                                continue;
                            } else {
                                for (PropID propId: resulte_after_operator) {
                                    if (cost < dual_StripsTask.h_value_for_single_propId[propId])
                                        cost = dual_StripsTask.h_value_for_single_propId[propId];
                                    for (PropID propId1: resulte_after_operator) {
                                        if (propId < propId1 &&
                                            cost < dual_StripsTask.h_value_for_pair[propId][propId1]) {
                                            cost = dual_StripsTask.h_value_for_pair[propId][propId1];
                                        }
                                    }
                                }
                            }
                            //takes the min for all operators
                            cost = cost + unaryOperator.base_cost;
                            if (cost < dual_StripsTask.h_value_for_single_propId[i]) {
                                dual_StripsTask.h_value_for_single_propId[i] = cost;
                                changed = true;

                            }
                        }
                    }
                }
                //sets value for pair of variables
                for (int j = i + 1; j < dual_StripsTask.h_value_for_single_propId.size(); ++j) {

                    //goes through all operators
                    for (UnaryOperator &unaryOperator: dual_StripsTask.unary_operators) {
                        //checks if delete effect is present
                        if (std::find(unaryOperator.del_effects.begin(), unaryOperator.del_effects.end(),
                                      i) != unaryOperator.del_effects.end() ||
                            std::find(unaryOperator.del_effects.begin(), unaryOperator.del_effects.end(),
                                      j) != unaryOperator.del_effects.end()) {
                        } else {
                            //an add effect must be present
                            bool i_or_j_is_included = false;
                            for(PropID propId : unaryOperator.add_effect){
                                if (propId == i || propId == j) {
                                    i_or_j_is_included = true;
                                    continue;
                                }
                            }
                            if (i_or_j_is_included){
                                //operator is used
                                vector <PropID> resulte_after_operator{i, j};

                                for(PropID propId : unaryOperator.add_effect){
                                    resulte_after_operator.erase(std::remove(resulte_after_operator.begin(), resulte_after_operator.end(), propId),
                                               resulte_after_operator.end());
                                }

                                resulte_after_operator.reserve((unaryOperator.preconditions.size()));
                                resulte_after_operator.insert(resulte_after_operator.end(), unaryOperator.preconditions.begin(),
                                            unaryOperator.preconditions.end());
                                utils::sort_unique(resulte_after_operator);


                                //takes min with temp.size() <= 2. with more it takes max
                                int cost = 0;
                                if (resulte_after_operator.size() == 1) {
                                    cost = dual_StripsTask.h_value_for_single_propId[resulte_after_operator[0]];
                                } else if (resulte_after_operator.size() == 2) {
                                    cost = dual_StripsTask.h_value_for_pair[resulte_after_operator[0]][resulte_after_operator[1]];
                                } else if (resulte_after_operator.size() < 1) {
                                    continue;
                                } else {
                                    for (PropID propId: resulte_after_operator) {
                                        if (cost < dual_StripsTask.h_value_for_single_propId[propId])
                                            cost = dual_StripsTask.h_value_for_single_propId[propId];
                                        for (PropID propId1: resulte_after_operator) {
                                            if (propId < propId1 &&
                                                cost < dual_StripsTask.h_value_for_pair[propId][propId1]) {
                                                cost = dual_StripsTask.h_value_for_pair[propId][propId1];

                                            }
                                        }
                                    }
                                }
                                //takes the min for all operators
                                cost = cost + unaryOperator.base_cost;
                                if (cost < dual_StripsTask.h_value_for_pair[i][j]) {
                                    dual_StripsTask.h_value_for_pair[i][j] = cost;
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    int Duality::compute_heuristic(const State &ancestor_state) {
        State state = convert_ancestor_state(ancestor_state);

        //setup_initial_state();
        //relaxed_exploration();


        int total_cost = 0;
        for (PropID goal_id : dual_StripsTask.goal_propositions) {
            total_cost = max(total_cost, dual_StripsTask.h_value_for_single_propId[goal_id]);
            for (PropID goal_id2 : dual_StripsTask.goal_propositions){

                if(goal_id < goal_id2){
                    total_cost = max(total_cost, dual_StripsTask.h_value_for_pair[goal_id][goal_id2]);
                }
            }
        }
        //std::cout << "total_cost  " << total_cost << std::endl;
        return total_cost;
    }


    static shared_ptr<Heuristic> _parse(OptionParser &parser) {
        Heuristic::add_options_to_parser(parser);
        Options opts = parser.parse();
        if (parser.dry_run())
            return nullptr;
        else
            return make_shared<Duality>(opts);
    }

    static Plugin<Evaluator> _plugin("dual", _parse);
}