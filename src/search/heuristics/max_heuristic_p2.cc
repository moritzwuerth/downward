//
// Created by moritz on 02.08.22.
//

#include "max_heuristic_p2.h"
#include "../option_parser.h"
#include "../plugin.h"

#include "../utils/logging.h"

#include <cassert>
#include <vector>

using namespace std;

namespace max_heuristic_p2 {
/*
  TODO: At the time of this writing, this shares huge amounts of code
        with h^add, and the two should be refactored so that the
        common code is only included once, in so far as this is
        possible without sacrificing run-time. We may want to avoid
        virtual calls in the inner-most loops; maybe a templated
        strategy pattern is an option. Right now, the only differences
        to the h^add code are the use of max() instead of add() and
        the lack of preferred operator support (but we might actually
        reintroduce that if it doesn't hurt performance too much).
 */

// construction and destruction
    HSPMaxHeuristic_P2::HSPMaxHeuristic_P2(const options::Options &opts)
        : Heuristic(opts) {

        //build p2_task
            normal_strips_Task = strips_task::Normal_Stripstask(task_proxy);
            p2_task = strips_task::StripsTask(normal_strips_Task);


        preconditions_pool = p2_task.preconditions_pool;
        // Cross-reference unary operators.
        vector<vector<OpID>> precondition_of_vectors(p2_task.propositions.size());
        int num_unary_ops = p2_task.unary_operators.size();
        for (OpID op_id = 0; op_id < num_unary_ops; ++op_id) {
            for (PropID precond: p2_task.get_preconditions(op_id)) {
                precondition_of_vectors[precond].push_back(op_id);
            }
        }

        int num_propositions = p2_task.propositions.size();
        for (PropID prop_id = 0; prop_id < num_propositions; ++prop_id) {
            const auto &precondition_of_vec = precondition_of_vectors[prop_id];
            p2_task.propositions[prop_id].precondition_of =
                    precondition_of_pool.append(precondition_of_vec);
            p2_task.propositions[prop_id].num_precondition_occurences = precondition_of_vec.size();
        }

    }

// heuristic computation
    void HSPMaxHeuristic_P2::setup_exploration_queue() {

        queue.clear();


        for (Proposition &prop : p2_task.propositions)
            prop.cost = -1;

        // Deal with operators and axioms without preconditions.
        for (UnaryOperator &op : p2_task.unary_operators) {
            op.unsatisfied_preconditions = op.num_preconditions;
            op.cost = op.base_cost; // will be increased by precondition costs

            if (op.unsatisfied_preconditions == 0) {
            enqueue_if_necessary(op.add_effect[0], op.base_cost);
                if (op.add_effect.size() > 1){
                    enqueue_if_necessary(op.add_effect[1], op.base_cost);
                }
            }
        }

    }

    void HSPMaxHeuristic_P2::setup_exploration_queue_state(const State &state) {

        for (PropID propId: p2_task.initial_propositions) {
            enqueue_if_necessary(propId, 0);

            for (PropID propId2 : p2_task.initial_propositions) {
                if (propId < propId2) {
                    enqueue_if_necessary(p2_task.prop_pairs2[propId][propId2], 0);

                }
            }
        }

    }

    void HSPMaxHeuristic_P2::relaxed_exploration() {
        int unsolved_goals = p2_task.goal_propositions.size();
        while (!queue.empty()) {
            pair<int, PropID> top_pair = queue.pop();
            int distance = top_pair.first;
            PropID prop_id = top_pair.second;
            Proposition *prop = p2_task.get_proposition(prop_id);
            int prop_cost = prop->cost;
            assert(prop_cost >= 0);
            assert(prop_cost <= distance);
            if (prop_cost < distance)
                continue;
            if (prop->is_goal && --unsolved_goals == 0)
                return;
            for (OpID op_id : precondition_of_pool.get_slice(
                    prop->precondition_of, prop->num_precondition_occurences)) {
                UnaryOperator *unary_op = p2_task.get_operator(op_id);
                unary_op->cost = max(unary_op->cost,
                                     unary_op->base_cost + prop_cost);
                --unary_op->unsatisfied_preconditions;
                assert(unary_op->unsatisfied_preconditions >= 0);
                if (unary_op->unsatisfied_preconditions == 0) {
                    enqueue_if_necessary(unary_op->add_effect[0], unary_op->cost);
                    if (unary_op->add_effect.size() > 1){
                        enqueue_if_necessary(unary_op->add_effect[1], unary_op->cost);
                    }
                }
            }

        }
    }

    int HSPMaxHeuristic_P2::compute_heuristic(const State &ancestor_state) {
        State state = convert_ancestor_state(ancestor_state);


        setup_exploration_queue();
        setup_exploration_queue_state(state);
        relaxed_exploration();

        int total_cost = 0;
        for (PropID goal_id : p2_task.goal_propositions) {
            const Proposition *goal = p2_task.get_proposition(goal_id);
            int goal_cost = goal->cost;
            if (goal_cost == -1)
                return DEAD_END;
            total_cost = max(total_cost, goal_cost);
        }
        //exit(total_cost);
        return total_cost;
    }

    static shared_ptr<Heuristic> _parse(OptionParser &parser) {
        Heuristic::add_options_to_parser(parser);
        Options opts = parser.parse();
        if (parser.dry_run())
            return nullptr;
        else
            return make_shared<HSPMaxHeuristic_P2>(opts);
    }


    static Plugin<Evaluator> _plugin("hmax_p2", _parse);


}