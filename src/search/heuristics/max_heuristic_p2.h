//
// Created by moritz on 02.08.22.
//

#ifndef HSPMAXHEURISTIC_P2_H2Heuristic_H
#define HSPMAXHEURISTIC_P2_H2Heuristic_H

//#include "relaxation_heuristic.h"

#include "../algorithms/priority_queues.h"
#include "h2_heuristic.h"
#include "strips_task.h"
#include "../heuristic.h"
#include <cassert>

namespace max_heuristic_p2 {
    using strips_task::PropID;
    using strips_task::OpID;
    using strips_task::Proposition;
    using strips_task::UnaryOperator;

    class HSPMaxHeuristic_P2 : public Heuristic {
        priority_queues::AdaptiveQueue<PropID> queue;

    protected:
        strips_task::StripsTask strips_Task;
        strips_task::StripsTask p2_task;
        //TODO std::vector<UnaryOperator> unary_operators;
        //TODO std::vector<Proposition> propositions;
        //TODO std::vector<PropID> goal_propositions;

        array_pool::ArrayPool preconditions_pool;
        array_pool::ArrayPool precondition_of_pool;


        void setup_exploration_queue();
        void setup_exploration_queue_state(const State &state);
        void relaxed_exploration();

        void enqueue_if_necessary(PropID prop_id, int cost) {
            assert(cost >= 0);
            Proposition *prop = p2_task.get_proposition(prop_id);
            if (prop->cost == -1 || prop->cost > cost) {
                prop->cost = cost;
                queue.push(cost, prop_id);
            }
            assert(prop->cost != -1 && prop->cost <= cost);
        }
    protected:
        virtual int compute_heuristic(const State &ancestor_state) override;
    public:
        explicit HSPMaxHeuristic_P2(const options::Options &options);
    };

}

#endif
