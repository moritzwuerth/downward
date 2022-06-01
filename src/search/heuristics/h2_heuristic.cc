#include "h2_heuristic.h"

#include "../option_parser.h"
#include "../plugin.h"

#include "../utils/logging.h"

#include "../task_utils/task_properties.h"

#include <iostream>
using namespace std;

namespace h2_heuristic {
Proposition::Proposition()
    : is_goal(false) {
}

UnaryOperator::UnaryOperator(
    int num_preconditions,
    vector<PropID> &&preconditions,
    PropID add_effect,
    int operator_no,
    int base_cost)
    : num_preconditions(num_preconditions),
      preconditions(move(preconditions)),
      add_effect(add_effect),
      operator_no(operator_no),
      base_cost(base_cost) {
}

H2Heuristic::H2Heuristic(const Options &opts)
    : Heuristic(opts) {
    if (log.is_at_least_normal()) {
        log << "Initializing h2 heuristic..." << endl;
    }

    if (log.is_at_least_debug()) {
        log << "Original SAS+ task:" << endl;
        task_properties::dump_task(task_proxy);
        log << "Operators:" << endl;
        for (OperatorProxy op : task_proxy.get_operators()) {
            log << op.get_name() << endl;
            log << "    preconditions: ";
            for (FactProxy precondition : op.get_preconditions()) {
                log << precondition.get_pair() << ", ";
            }
            log << endl;
            log << "    effects: " << endl;
            for (EffectProxy effect : op.get_effects()) {
                log << "        effect: " << effect.get_fact().get_pair() << endl;
                log << "        condition: ";
                for (FactProxy eff_cond : effect.get_conditions()) {
                    log << eff_cond.get_pair() << ", ";
                }
                log << endl;
            }
        }
    }

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

    if (log.is_at_least_debug()) {
        log << "Computed STRIPS task:" << endl;
        log << "Propositions:" << endl;
        for (const Proposition &prop : propositions) {
            log << "PropID " << get_prop_id(prop) << "; is goal? " << prop.is_goal << endl;
        }
        log << "Operators:" << endl;
        for (const UnaryOperator &op : unary_operators) {
            log << "    OpID " << get_op_id(op) << ":" << endl;
            log << "    num preconditions: " << op.num_preconditions << endl;
            log << "    preconditions: " << op.preconditions << endl;
            log << "    add effect: " << op.add_effect << endl;
            log << "    original operator no: " << op.operator_no << endl;
            log << "    original operator cost: " << op.base_cost << endl;
        }
    }
}

void H2Heuristic::build_unary_operators(const OperatorProxy &op) {
    assert(!op.is_axiom());
    int op_no = op.is_axiom() ? -1 : op.get_id();
    int base_cost = op.get_cost();
    vector<PropID> precondition_props;
    PreconditionsProxy preconditions = op.get_preconditions();
    precondition_props.reserve(preconditions.size());
    for (FactProxy precondition : preconditions) {
        precondition_props.push_back(get_prop_id(precondition));
    }
    for (EffectProxy effect : op.get_effects()) {
        PropID effect_prop = get_prop_id(effect.get_fact());
        EffectConditionsProxy eff_conds = effect.get_conditions();
        precondition_props.reserve(preconditions.size() + eff_conds.size());
        for (FactProxy eff_cond : eff_conds) {
            precondition_props.push_back(get_prop_id(eff_cond));
        }

        // The sort-unique can eventually go away. See issue497.
        vector<PropID> preconditions_copy(precondition_props);
        utils::sort_unique(preconditions_copy);
        unary_operators.emplace_back(
            preconditions_copy.size(), move(preconditions_copy), effect_prop,
            op_no, base_cost);
        precondition_props.erase(precondition_props.end() - eff_conds.size(), precondition_props.end());
    }
}

int H2Heuristic::compute_heuristic(const State &ancestor_state) {
    State state = convert_ancestor_state(ancestor_state);
    // TODO
    return 0;
}

PropID H2Heuristic::get_prop_id(int var, int value) const {
    return proposition_offsets[var] + value;
}

PropID H2Heuristic::get_prop_id(const FactProxy &fact) const {
    return get_prop_id(fact.get_variable().get_id(), fact.get_value());
}

const Proposition *H2Heuristic::get_proposition(
    int var, int value) const {
    return &propositions[get_prop_id(var, value)];
}

Proposition *H2Heuristic::get_proposition(int var, int value) {
    return &propositions[get_prop_id(var, value)];
}

Proposition *H2Heuristic::get_proposition(const FactProxy &fact) {
    return get_proposition(fact.get_variable().get_id(), fact.get_value());
}

static shared_ptr<Heuristic> _parse(OptionParser &parser) {
    Heuristic::add_options_to_parser(parser);
    Options opts = parser.parse();
    if (parser.dry_run())
        return nullptr;
    else
        return make_shared<H2Heuristic>(opts);
}


static Plugin<Evaluator> _plugin("h2", _parse);
}
