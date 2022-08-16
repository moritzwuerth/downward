//
// Created by moritz on 18.07.22.
//
#ifndef STRIPS_TASK_H
#define STRIPS_TASK_H


#include "../evaluator.h"

#include "../task_proxy.h"
#include "array_pool.h"

#include "../utils/collections.h"
#include <unordered_map>
#include <memory>
#include <vector>

namespace strips_task {
struct Proposition;
struct UnaryOperator;

using PropID = int;
using OpID = int;
using Prop_Original_Size = int;
const OpID NO_OP = -1;

struct Proposition {
    Proposition();
    int cost;
    bool is_goal;
    int num_precondition_occurences;
    array_pool::ArrayPoolIndex precondition_of;
};

struct UnaryOperator {
    UnaryOperator(int num_preconditions,
                  std::vector<PropID> &&preconditions,
                  std::vector<PropID> &&add_effect,
                  int num_del_effects,
                  std::vector<PropID> &&del_effects,
                  int operator_no,
                  int base_cost);
    int num_preconditions;
    std::vector<PropID> preconditions;
    std::vector<PropID> add_effect;
    int num_del_effects;
    std::vector<PropID> del_effects;
    int operator_no; // -1 for axioms; index into the task's operators otherwise
    int base_cost;

    int cost; // Used for h^max cost or h^add cost;
    // includes operator cost (base_cost)
    int unsatisfied_preconditions;
};

class StripsTask {
public:
    // proposition_offsets[var_no]: first PropID related to variable var_no
    std::vector<PropID> proposition_offsets;
    std::vector<UnaryOperator> unary_operators;
    std::vector<Proposition> propositions;
    std::vector<PropID> goal_propositions;
    std::unordered_map<std::string,std::unordered_map<std::string, int>> prop_pairs;
    Prop_Original_Size original_size;
    std::vector<PropID> original_propIDs;
    std::vector<std::vector<PropID>> prop_pairs2;

    array_pool::ArrayPool preconditions_pool;
    array_pool::ArrayPool precondition_of_pool;

    void build_unary_operators(const OperatorProxy &op);

/*protected:
    virtual int compute_heuristic(const State &ancestor_state) override;*/
public:
    explicit StripsTask(const TaskProxy &task_proxy);
    explicit StripsTask();


        /*
          TODO: Some of these protected methods are only needed for the
          CEGAR hack in the additive heuristic and should eventually go
          away.
        */



    PropID get_prop_id(const Proposition &prop) const {
        PropID prop_id = &prop - propositions.data();
        //assert(utils::in_bounds(prop_id, propositions));
        return prop_id;
    }

    OpID get_op_id(const UnaryOperator &op) const {
        OpID op_id = &op - unary_operators.data();
        assert(utils::in_bounds(op_id, unary_operators));
        return op_id;
    }

    PropID get_prop_id(int var, int value) const;
    PropID get_prop_id(const FactProxy &fact) const;

    Proposition *get_proposition(PropID prop_id) {
        return &propositions[prop_id];
    }
    UnaryOperator *get_operator(OpID op_id) {
        return &unary_operators[op_id];
    }

    const Proposition *get_proposition(int var, int value) const;
    Proposition *get_proposition(int var, int value);
    Proposition *get_proposition(const FactProxy &fact);


    StripsTask build_p2_strips_task(StripsTask &stripsTask);

    void build_goal_propositions(std::vector<PropID> &goal_propids);

    std::vector<PropID> build_f(std::vector<PropID> &effects, std::vector<PropID> &del_effects);

    void build_prop_pairs();

    void insert_propid(std::vector<PropID> &vector, PropID x, PropID y);

    void rebuild_unaryopearator();

    std::vector<PropID> get_preconditions(OpID &opId);

};
}

#endif
