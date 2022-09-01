//
// Created by moritz on 23.08.22.
//

#ifndef DUALITY_Heuristic_H
#define DUALITY_Heuristic_H

#include "../algorithms/priority_queues.h"
#include "../heuristic.h"
#include <cassert>
#include "strips_task.h"

namespace dual {
    using strips_task::PropID;
    using strips_task::OpID;
    using strips_task::Proposition;
    using strips_task::UnaryOperator;

    class Duality :public Heuristic {
        priority_queues::AdaptiveQueue<PropID> queue;

    protected:
        strips_task::StripsTask strips_Task;
        std::vector<PropID> old_goal;


    void setup_initial_state();
    void relaxed_exploration();


    protected:
        virtual int compute_heuristic(const State &ancestor_state) override;
    public:
        explicit Duality(const options::Options &options);
    };
}

#endif
