#include "h2_heuristic.h"

#include "../option_parser.h"
#include "../plugin.h"

#include "../utils/logging.h"

#include <iostream>
using namespace std;

namespace h2_heuristic {
H2Heuristic::H2Heuristic(const Options &opts)
    : Heuristic(opts) {
    if (log.is_at_least_normal()) {
        log << "Initializing h2 heuristic..." << endl;
    }
}

int H2Heuristic::compute_heuristic(const State &ancestor_state) {
    State state = convert_ancestor_state(ancestor_state);
    // TODO
    return 0;
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
