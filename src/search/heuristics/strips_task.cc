//
// Created by moritz on 18.07.22.
//

#include "strips_task.h"

#include "../option_parser.h"
#include "../plugin.h"

#include "../utils/logging.h"

#include "../task_utils/task_properties.h"

#include <iostream>
using namespace std;

namespace strips_task{

    Proposition::Proposition()
            : cost(-1),
            is_goal(false) {
    }

    UnaryOperator::UnaryOperator(
            int num_preconditions,
            vector <PropID> &&preconditions,
            vector <PropID> &&add_effect,
            int num_del_effects,
            vector <PropID> &&del_effects,
            int operator_no,
            int base_cost)
            : num_preconditions(num_preconditions),
              preconditions(move(preconditions)),
              add_effect(add_effect),
              num_del_effects(num_del_effects),
              del_effects(move(del_effects)),
              operator_no(operator_no),
              base_cost(base_cost) {
    }

    StripsTask::StripsTask() {
    }

    StripsTask::StripsTask(Normal_Stripstask &normal_stripstask){    //TODO name p2_stripstask

        propositions = normal_stripstask.propositions;
        build_prop_pairs();
        build_goal_propositions(normal_stripstask.goal_propositions);

        vector<UnaryOperator> new_unaryOperators;

        for (UnaryOperator &unaryOperator : normal_stripstask.unary_operators) {

            vector <PropID> f;
            f = build_f(unaryOperator.add_effect, unaryOperator.del_effects);
            vector <PropID> new_precondition_props;
            vector<PropID> new_add_effects;

            for (PropID &f: f) {
                new_precondition_props = unaryOperator.preconditions;
                new_add_effects = unaryOperator.add_effect;
                new_precondition_props.push_back(f);
                for (PropID propId: unaryOperator.preconditions) {
                    insert_propid(new_precondition_props, f, propId);
                }

                for (PropID &propId1 : unaryOperator.preconditions) {
                    for (PropID propId2: unaryOperator.preconditions) {
                        if (propId1 < propId2) {
                            new_precondition_props.push_back(prop_pairs2[propId1][propId2]);
                        }
                    }
                }

                unaryOperator.del_effects.clear();
                insert_propid(new_add_effects, f, new_add_effects[0]);


                // The sort-unique can eventually go away. See issue497.
                vector <PropID> preconditions_copy(new_precondition_props);
                vector <PropID> del_effects_copy(unaryOperator.del_effects);
                vector<PropID> add_effects_copy(new_add_effects);
                utils::sort_unique(preconditions_copy);
                utils::sort_unique(add_effects_copy);
                new_unaryOperators.emplace_back(preconditions_copy.size(), move(preconditions_copy), move(add_effects_copy),
                                                del_effects_copy.size(), move(del_effects_copy), unaryOperator.operator_no, unaryOperator.base_cost);
                //precondition_props.erase(precondition_props.end() - eff_conds.size(), precondition_props.end());
            }
        }
        unary_operators = new_unaryOperators;
        initial_propositions = normal_stripstask.initial_propositions;




    }


    PropID StripsTask::get_prop_id(int var, int value) const {
        return proposition_offsets[var] + value;
    }

    PropID StripsTask::get_prop_id(const FactProxy &fact) const {
        return get_prop_id(fact.get_variable().get_id(), fact.get_value());
    }

    const Proposition *StripsTask::get_proposition(
            int var, int value) const {
        return &propositions[get_prop_id(var, value)];
    }

    Proposition *StripsTask::get_proposition(int var, int value) {
        return &propositions[get_prop_id(var, value)];
    }

    Proposition *StripsTask::get_proposition(const FactProxy &fact) {
        return get_proposition(fact.get_variable().get_id(), fact.get_value());
    }




    void StripsTask::build_goal_propositions(vector<PropID> &goal_propids){
        vector<PropID> new_goal_propositions;
        for (PropID &propId : goal_propids){
            new_goal_propositions.push_back(propId);
            for (PropID &propId2 : goal_propids) {
                if (propId < propId2)
                    insert_propid(new_goal_propositions, propId2, propId);
            }
        }
        for (PropID propid: new_goal_propositions) {
            get_proposition(propid)->is_goal = true;
        }
        goal_propositions = new_goal_propositions;
    }


    void StripsTask::insert_propid(vector<PropID> &vector, PropID x, PropID y){
        if (x > y) {
            vector.push_back(prop_pairs2[y][x]);
        }else if (x < y) {
            vector.push_back(prop_pairs2[x][y]);
        }
    }

    vector<PropID> StripsTask::build_f(vector<PropID> &effects, vector<PropID> &del_effects) {

        for (PropID propId: effects) {
            del_effects.push_back(propId);
        }
        vector<PropID> f;
        for (PropID &propId: original_propIDs) {
            if (std::find(del_effects.begin(), del_effects.end(), propId) != del_effects.end()) {
            } else {
                f.push_back(propId);
            }
        }

        return f;
    }

    void StripsTask::build_prop_pairs(){
        prop_pairs2.resize(propositions.size(), vector<PropID>(propositions.size()));
        int new_propId = propositions.size();
        for (Proposition &prop: propositions) {

            original_propIDs.push_back(get_prop_id(prop));

            for (Proposition &prop2: propositions) {
                if (get_prop_id(prop) < get_prop_id(prop2)) {
                    prop_pairs2[get_prop_id(prop)][get_prop_id(prop2)] = new_propId;
                    new_propId++;
                }
            }
        }
        propositions.resize(new_propId);
    }
    void StripsTask::rebuild_unaryopearator(){
        vector<UnaryOperator> new_unaryOperators;
        for (UnaryOperator &unaryOperator : unary_operators){

            if (unaryOperator.add_effect.size() > 1) {
                vector<PropID> add_effect;

                UnaryOperator new_unaryOperator = unaryOperator;

                add_effect.push_back(unaryOperator.add_effect[0]);
                new_unaryOperator.add_effect = add_effect;
                preconditions_pool.append(new_unaryOperator.preconditions);
                new_unaryOperators.emplace_back(new_unaryOperator);


                add_effect.clear();

                add_effect.push_back(unaryOperator.add_effect[1]);
                new_unaryOperator.add_effect = add_effect;
                preconditions_pool.append(new_unaryOperator.preconditions);
                new_unaryOperators.emplace_back(new_unaryOperator);

            }
        }
        unary_operators = new_unaryOperators;
    }


    std::vector<PropID> StripsTask::get_preconditions(OpID &opId){
        return unary_operators[opId].preconditions;
    }





    Normal_Stripstask::Normal_Stripstask() {}

    Normal_Stripstask::Normal_Stripstask(TaskProxy &task_proxy) {
        // Build propositions.
        propositions.resize(task_properties::get_num_facts(task_proxy));

        // Build proposition offsets.
        VariablesProxy variables = task_proxy.get_variables();
        proposition_offsets.reserve(variables.size());
        PropID offset = 0;
        for (VariableProxy var : variables) {
            proposition_offsets.push_back(offset);
            offset += var.get_domain_size();
        }
        assert(offset == static_cast<int>(propositions.size()));

        // Build goal propositions.
        GoalsProxy goals = task_proxy.get_goals();
        goal_propositions.reserve(goals.size());
        for (FactProxy goal : goals) {
            PropID prop_id = get_prop_id(goal);
            propositions[prop_id].is_goal = true;
            goal_propositions.push_back(prop_id);
        }

        // Build unary operators for operators and axioms.
        unary_operators.reserve(
                task_properties::get_num_total_effects(task_proxy));
        for (OperatorProxy op : task_proxy.get_operators())
            build_unary_operators(op);

        // Build initial propositions
        State state = task_proxy.get_initial_state();
        for (FactProxy fact : state){
            initial_propositions.push_back(get_prop_id(fact));
        }
    }

    void Normal_Stripstask::build_unary_operators(const OperatorProxy &op) {
        assert(!op.is_axiom());
        int op_no = op.is_axiom() ? -1 : op.get_id();
        int base_cost = op.get_cost();
        vector<PropID> precondition_props;
        vector<PropID> delcondition_prop;

        vector<PropID> delcondition_normal;
        vector<PropID> add_effects_normal;
        vector<PropID> precondition_normal;
        PreconditionsProxy preconditions = op.get_preconditions();
        precondition_props.reserve(preconditions.size());
        for (FactProxy precondition : preconditions) {
            precondition_props.push_back(get_prop_id(precondition));
        }
        for (EffectProxy effect : op.get_effects()) {
            PropID effect_prop = get_prop_id(effect.get_fact());
            vector<PropID> effects;
            effects.push_back(get_prop_id(effect.get_fact()));
            EffectConditionsProxy eff_conds = effect.get_conditions();
            precondition_props.reserve(preconditions.size() + eff_conds.size());
            for (FactProxy eff_cond : eff_conds) {
                precondition_props.push_back(get_prop_id(eff_cond));
            }

            int first_propId_var = proposition_offsets[effect.get_fact().get_variable().get_id()];
            int var_domain_size = effect.get_fact().get_variable().get_domain_size();
            delcondition_prop.clear();
            delcondition_normal.clear();
            delcondition_prop.reserve(var_domain_size - 1);

            for (int i = first_propId_var; i < first_propId_var + var_domain_size; ++i) {
                if (i != effect_prop) {
                    if (std::find(precondition_props.begin(), precondition_props.end(), i) != precondition_props.end()) {
                        delcondition_prop.push_back(i);
                        delcondition_normal.push_back(i);
                    }
                }
            }
            add_effects_normal.push_back(get_prop_id(effect.get_fact()));
            precondition_normal = precondition_props;

            // The sort-unique can eventually go away. See issue497.
            vector <PropID> preconditions_copy(precondition_props);
            vector <PropID> del_effects_copy(delcondition_prop);
            utils::sort_unique(preconditions_copy);
            utils::sort_unique(del_effects_copy);
            unary_operators.emplace_back(preconditions_copy.size(), move(preconditions_copy), move(effects),
                                         del_effects_copy.size(), move(del_effects_copy), op_no, base_cost);
            precondition_props.erase(precondition_props.end() - eff_conds.size(), precondition_props.end());
        }
        operators.emplace_back(precondition_normal.size(), move(precondition_normal), move(add_effects_normal),
                               delcondition_normal.size(), move(delcondition_normal), op_no, base_cost);
        //precondition_props.erase(precondition_props.end() - eff_conds.size(), precondition_props.end());
    }

    Dual_StripsTask::Dual_StripsTask() {}

    Dual_StripsTask::Dual_StripsTask(Normal_Stripstask &normal_stripstask) {
        propositions = normal_stripstask.propositions;
        h_value_for_single_propId.resize(normal_stripstask.propositions.size());
        build_dual_pairs();
        unary_operators = normal_stripstask.operators;
        //unary_operators = normal_stripstask.unary_operators;
        unaryoperator_exchanging_roles();
        initial_propositions = dual_initial_state(normal_stripstask.goal_propositions);
        goal_propositions = dual_goal(normal_stripstask.initial_propositions);

    }

    void Dual_StripsTask::unaryoperator_exchanging_roles(){
        vector<PropID> temp_precondition;
        for (UnaryOperator &unaryOperator: unary_operators) {
            temp_precondition = unaryOperator.preconditions;
            unaryOperator.preconditions = unaryOperator.del_effects;
            unaryOperator.del_effects = temp_precondition;
        }
    }

    vector<PropID> Dual_StripsTask::dual_goal(vector<PropID> &old_initial_propIds) {
        vector <PropID> new_goal_propositions;

        vector<PropID> all_propIds;

        for (Proposition &proposition: propositions){
            all_propIds.push_back(get_prop_id(proposition));
        }

        for (PropID &propId: all_propIds) {
            if (std::find(old_initial_propIds.begin(), old_initial_propIds.end(), propId) != old_initial_propIds.end()) {
            } else {
                new_goal_propositions.push_back(propId);
            }
        }

        return new_goal_propositions;
    }


    vector<PropID> Dual_StripsTask::dual_initial_state(vector<PropID> &old_goal_propositions) {
        vector<PropID> new_initial_propIds;

        for (Proposition &proposition : propositions) {
            if (std::find(old_goal_propositions.begin(), old_goal_propositions.end(), get_prop_id(proposition)) != old_goal_propositions.end()) {
            } else {
                new_initial_propIds.push_back(get_prop_id(proposition));
            }
        }
        return new_initial_propIds;

    }

    void Dual_StripsTask::build_dual_pairs() {
        h_value_for_pair.resize(propositions.size(), vector<PropID>(propositions.size()));
        h_value_for_single_propId.resize(propositions.size());
        for (Proposition &prop: propositions) {

            //std::numeric_limits<int>::max() does not work, otherwise a minus value appears, therefore a random high value;
            h_value_for_single_propId[get_prop_id(prop)] =  1000000;

            for (Proposition &prop2: propositions) {
                if (get_prop_id(prop) < get_prop_id(prop2)) {
                    h_value_for_pair[get_prop_id(prop)][get_prop_id(prop2)] = 1000000;
                }
            }
        }
    }

    PropID Normal_Stripstask::get_prop_id(const FactProxy &fact) const {
        return get_prop_id(fact.get_variable().get_id(), fact.get_value());
    }

    PropID Normal_Stripstask::get_prop_id(int var, int value) const {
        return proposition_offsets[var] + value;
    }




}



