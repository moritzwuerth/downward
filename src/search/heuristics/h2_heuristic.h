#ifndef HEURISTICS_H2_HEURISTIC_H
#define HEURISTICS_H2_HEURISTIC_H

#include "../heuristic.h"

namespace h2_heuristic {
class H2Heuristic : public Heuristic {
protected:
    virtual int compute_heuristic(const State &ancestor_state) override;
public:
    explicit H2Heuristic(const options::Options &opts);
};
}

#endif
