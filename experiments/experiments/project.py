from pathlib import Path
import platform
import subprocess
import sys

from downward.experiment import FastDownwardExperiment
from downward.reports.absolute import AbsoluteReport
from downward.reports.scatter import ScatterPlotReport
from downward.reports.taskwise import TaskwiseReport
from lab import tools
from lab.environments import (
    BaselSlurmEnvironment,
    LocalEnvironment,
    TetralithEnvironment,
)
from lab.experiment import ARGPARSER
from lab.reports import Attribute, geometric_mean


# Silence import-unused messages. Experiment scripts may use these imports.
assert (
    BaselSlurmEnvironment
    and FastDownwardExperiment
    and LocalEnvironment
    and ScatterPlotReport
    and TaskwiseReport
    and TetralithEnvironment
)


DIR = Path(__file__).resolve().parent
NODE = platform.node()
REMOTE = NODE.endswith((".scicore.unibas.ch", ".cluster.bc2.ch"))


def parse_args():
    ARGPARSER.add_argument("--tex", action="store_true", help="produce LaTeX output")
    ARGPARSER.add_argument(
        "--relative", action="store_true", help="make relative scatter plots"
    )
    return ARGPARSER.parse_args()


ARGS = parse_args()
TEX = ARGS.tex
RELATIVE = ARGS.relative

# Generated by "./suites.py satisficing" in aibasel/downward-benchmarks repo.
# fmt: off
SUITE_SATISFICING = [
    "agricola-sat18-strips", "airport", "assembly", "barman-sat11-strips",
    "barman-sat14-strips", "blocks", "caldera-sat18-adl",
    "caldera-split-sat18-adl", "cavediving-14-adl", "childsnack-sat14-strips",
    "citycar-sat14-adl", "data-network-sat18-strips", "depot", "driverlog",
    "elevators-sat08-strips", "elevators-sat11-strips", "flashfill-sat18-adl",
    "floortile-sat11-strips", "floortile-sat14-strips", "freecell",
    "ged-sat14-strips", "grid", "gripper", "hiking-sat14-strips",
    "logistics00", "logistics98", "maintenance-sat14-adl", "miconic",
    "miconic-fulladl", "miconic-simpleadl", "movie", "mprime", "mystery",
    "nomystery-sat11-strips", "nurikabe-sat18-adl", "openstacks",
    "openstacks-sat08-adl", "openstacks-sat08-strips",
    "openstacks-sat11-strips", "openstacks-sat14-strips", "openstacks-strips",
    "optical-telegraphs", "organic-synthesis-sat18-strips",
    "organic-synthesis-split-sat18-strips", "parcprinter-08-strips",
    "parcprinter-sat11-strips", "parking-sat11-strips", "parking-sat14-strips",
    "pathways", "pegsol-08-strips", "pegsol-sat11-strips", "philosophers",
    "pipesworld-notankage", "pipesworld-tankage", "psr-large", "psr-middle",
    "psr-small", "rovers", "satellite", "scanalyzer-08-strips",
    "scanalyzer-sat11-strips", "schedule", "settlers-sat18-adl",
    "snake-sat18-strips", "sokoban-sat08-strips", "sokoban-sat11-strips",
    "spider-sat18-strips", "storage", "termes-sat18-strips",
    "tetris-sat14-strips", "thoughtful-sat14-strips", "tidybot-sat11-strips",
    "tpp", "transport-sat08-strips", "transport-sat11-strips",
    "transport-sat14-strips", "trucks", "trucks-strips",
    "visitall-sat11-strips", "visitall-sat14-strips",
    "woodworking-sat08-strips", "woodworking-sat11-strips", "zenotravel",
]
SUITE_OPTIMAL = ["agricola-opt18-strips", "airport", "barman-opt11-strips", "barman-opt14-strips", "blocks", "childsnack-opt14-strips", "data-network-opt18-strips", "depot", "driverlog", "elevators-opt08-strips", "elevators-opt11-strips", "floortile-opt11-strips", "floortile-opt14-strips", "freecell", "ged-opt14-strips", "grid", "gripper", "hiking-opt14-strips", "logistics00", "logistics98", "miconic", "movie", "mprime", "mystery", "nomystery-opt11-strips", "openstacks-opt08-strips", "openstacks-opt11-strips", "openstacks-opt14-strips", "openstacks-strips", "organic-synthesis-opt18-strips", "organic-synthesis-split-opt18-strips", "parcprinter-08-strips", "parcprinter-opt11-strips", "parking-opt11-strips", "parking-opt14-strips", "pathways", "pegsol-08-strips", "pegsol-opt11-strips", "petri-net-alignment-opt18-strips", "pipesworld-notankage", "pipesworld-tankage", "psr-small", "rovers", "satellite", "scanalyzer-08-strips", "scanalyzer-opt11-strips", "snake-opt18-strips", "sokoban-opt08-strips", "sokoban-opt11-strips", "spider-opt18-strips", "storage", "termes-opt18-strips", "tetris-opt14-strips", "tidybot-opt11-strips", "tidybot-opt14-strips", "tpp", "transport-opt08-strips", "transport-opt11-strips", "transport-opt14-strips", "trucks-strips", "visitall-opt11-strips", "visitall-opt14-strips", "woodworking-opt08-strips", "woodworking-opt11-strips", "zenotravel"]

# fmt: on


def get_repo_base() -> Path:
    """Get base directory of the repository, as an absolute path.

    Search upwards in the directory tree from the main script until a
    directory with a subdirectory named ".git" is foun= []d.

    Abort if the repo base cannot be found."""
    path = Path(tools.get_script_path())
    while path.parent != path:
        if (path / ".git").is_dir():
            return path
        path = path.parent
    sys.exit("repo base could not be found")


def remove_file(path: Path):
    try:
        path.unlink()
    except FileNotFoundError:
        pass


def _get_exp_dir_relative_to_repo():
    repo_name = get_repo_base().name
    script = Path(tools.get_script_path())
    script_dir = script.parent
    rel_script_dir = script_dir.relative_to(get_repo_base())
    expname = script.stem
    return repo_name / rel_script_dir / "data" / expname


def add_absolute_report(exp, *, name=None, outfile=None, **kwargs):
    report = AbsoluteReport(**kwargs)
    if name and not outfile:
        outfile = f"{name}.{report.output_format}"
    elif outfile and not name:
        name = Path(outfile).name
    elif not name and not outfile:
        name = f"{exp.name}-abs"
        outfile = f"{name}.{report.output_format}"

    if not Path(outfile).is_absolute():
        outfile = Path(exp.eval_dir) / outfile

    exp.add_report(report, name=name, outfile=outfile)
