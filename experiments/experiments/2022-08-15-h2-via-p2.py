#! /usr/bin/env python

import os
import shutil

import project


REPO = project.get_repo_base()
BENCHMARKS_DIR = "/home/moritz/Schreibtisch/H2_Heuristic/benchmarks"
if project.REMOTE:
    SUITE = project.SUITE_OPTIMAL
    ENV = project.BaselSlurmEnvironment(email="moritz.wuerth@stud.unibas.ch")
else:
    SUITE = ["depot:p01.pddl", "grid:prob01.pddl", "gripper:prob01.pddl"]
    ENV = project.LocalEnvironment(processes=2)


# (f"{index:02d}-{h_nick}", ["--search", f"eager_greedy([{h}])"])

CONFIGS = [
    ("h2-default", ["--search", "astar(hm(2))"]),
    ("h2-via-p2", ["--search", "astar(eval=hmax_p2())"]),
]
BUILD_OPTIONS = []
DRIVER_OPTIONS = ["--overall-time-limit", "5m"]
REVS = [
    "b3ad9ab5d9818ae093a306e51473012689b740b2",
]
ATTRIBUTES = [
    "error",
    "run_dir",
    "search_time",
    "total_time",
    "coverage",
    "expansions",
    "expansions_until_last_jump",
    "memory",
    "initial_h_value",
]

exp = project.FastDownwardExperiment(environment=ENV)
for config_nick, config in CONFIGS:
    for rev in REVS:
        algo_name = f"{rev}-{config_nick}"
        exp.add_algorithm(
            algo_name,
            REPO,
            rev,
            config,
            build_options=BUILD_OPTIONS,
            driver_options=DRIVER_OPTIONS,
        )
exp.add_suite(BENCHMARKS_DIR, SUITE)

exp.add_parser(exp.EXITCODE_PARSER)
exp.add_parser(exp.TRANSLATOR_PARSER)
exp.add_parser(exp.SINGLE_SEARCH_PARSER)
exp.add_parser(exp.PLANNER_PARSER)

exp.add_step("build", exp.build)
exp.add_step("start", exp.start_runs)
exp.add_fetcher(name="fetch")

project.add_absolute_report(
    exp, attributes=ATTRIBUTES,
)

exp.run_steps()
