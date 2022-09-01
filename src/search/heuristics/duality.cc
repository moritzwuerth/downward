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
        strips_Task = strips_task::StripsTask(task_proxy);

        //swaps pre and del in the operators
        strips_Task.unaryoperator_exchanging_roles();

        //makes dual initial and goal state
        strips_Task.old_goal_propositions = strips_Task.goal_propositions;
        State state = task_proxy.get_initial_state();
        strips_Task.dual_goal(state);

        strips_Task.build_dual_pairs();

    }
    void Duality::setup_initial_state() {
        vector<PropID> initial_propIds = strips_Task.dual_initial_state();

        for (PropID &propId : initial_propIds){
            strips_Task.original_propIDs[propId] = 0;

            for (PropID &propId2 : initial_propIds) {
                if (propId < propId2) {
                    strips_Task.prop_pairs2[propId][propId2] = 0;
                }
            }
        }
    }

    void Duality::relaxed_exploration() {


        //sets value for individual variables
        for (int i = 0; i < strips_Task.original_propIDs.size(); ++i) {

            //goes through all operators
            for (UnaryOperator &unaryOperator: strips_Task.unary_operators) {

                //checks if delete effect is present
                if (std::find(unaryOperator.del_effects.begin(), unaryOperator.del_effects.end(),
                              i) != unaryOperator.del_effects.end()) {
                } else {
                    //an add effect must be present
                    if (unaryOperator.add_effect[0] == i) {
                        vector <PropID> temp{i};

                        //operator is used (regression)
                        temp.erase(std::remove(temp.begin(), temp.end(), unaryOperator.add_effect[0]), temp.end());
                        temp.reserve((unaryOperator.preconditions.size()));
                        temp.insert(temp.end(), unaryOperator.preconditions.begin(),
                                    unaryOperator.preconditions.end());
                        utils::sort_unique(temp);

                        //takes min with temp.size() <= 2. with more it takes max
                        int cost = 0;
                        if (temp.size() == 1) {
                            cost = strips_Task.original_propIDs[temp[0]];
                        } else if (temp.size() == 2) {
                            cost = strips_Task.prop_pairs2[temp[0]][temp[1]];
                        }else if (temp.size() < 1){
                            continue;
                        } else {
                            for (PropID propId: temp) {
                                if (cost < strips_Task.original_propIDs[propId])
                                    cost = strips_Task.original_propIDs[propId];
                                for (PropID propId1: temp) {
                                    if (propId < propId1 && cost < strips_Task.prop_pairs2[propId][propId1]) {
                                        cost = strips_Task.prop_pairs2[propId][propId1];
                                    }
                                }
                            }
                        }
                        //takes the min for all operators
                        cost = cost + unaryOperator.base_cost;
                        if (cost < strips_Task.original_propIDs[i]) {
                            strips_Task.original_propIDs[i] = cost;
                        }
                    }
                }
            }
            //sets value for pair of variables
            for (int j = i + 1; j < strips_Task.original_propIDs.size(); ++j) {

                //goes through all operators
                for (UnaryOperator &unaryOperator: strips_Task.unary_operators) {
                    //checks if delete effect is present
                    if (std::find(unaryOperator.del_effects.begin(), unaryOperator.del_effects.end(),
                                  i) != unaryOperator.del_effects.end()||
                            std::find(unaryOperator.del_effects.begin(), unaryOperator.del_effects.end(),
                                      j) != unaryOperator.del_effects.end()) {
                    } else {
                        //an add effect must be present
                        if (unaryOperator.add_effect[0] == i || unaryOperator.add_effect[0] == j) {


                            //operator is used
                            vector <PropID> temp{i, j};

                            temp.erase(std::remove(temp.begin(), temp.end(), unaryOperator.add_effect[0]), temp.end());

                            temp.reserve((unaryOperator.preconditions.size()));
                            temp.insert(temp.end(), unaryOperator.preconditions.begin(),
                                        unaryOperator.preconditions.end());

                            utils::sort_unique(temp);

                            //takes min with temp.size() <= 2. with more it takes max
                            int cost = 0;
                            if (temp.size() == 1) {
                                cost = strips_Task.original_propIDs[temp[0]];
                            } else if (temp.size() == 2) {
                                cost = strips_Task.prop_pairs2[temp[0]][temp[1]];
                            }else if (temp.size() < 1){
                                continue;
                            } else {
                                for (PropID propId: temp) {
                                    if (cost < strips_Task.original_propIDs[propId])
                                        cost = strips_Task.original_propIDs[propId];
                                    for (PropID propId1: temp) {
                                        if (propId < propId1 && cost < strips_Task.prop_pairs2[propId][propId1]) {
                                            cost = strips_Task.prop_pairs2[propId][propId1];
                                        }
                                    }
                                }
                            }
                            //takes the min for all operators
                            cost = cost + unaryOperator.base_cost;
                            if (cost < strips_Task.prop_pairs2[i][j]) {
                                strips_Task.prop_pairs2[i][j] = cost;
                            }
                        }
                    }
                }
            }
        }
    }


    int Duality::compute_heuristic(const State &ancestor_state) {
        State state = convert_ancestor_state(ancestor_state);


        setup_initial_state();
        relaxed_exploration();


        int total_cost = 0;
        for (PropID goal_id : strips_Task.goal_propositions) {
            total_cost = max(total_cost, strips_Task.original_propIDs[goal_id]);
            for (PropID goal_id2 : strips_Task.goal_propositions){

                if(goal_id < goal_id2){
                    total_cost = max(total_cost, strips_Task.prop_pairs2[goal_id][goal_id2]);
                }
            }
        }
        std::cout << "total_cost  " << total_cost << std::endl;
        return total_cost;
    }


    /*int H2Heuristic::compute_heuristic(const State &ancestor_state) {
        State state = convert_ancestor_state(ancestor_state);
        // TODO
        return 0;
    }*/

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