

import PyBoolNet


def test_ef_subspaces():
    subspaces = [{"v1": 0, "v2": 0}, {"v1": 1, "v2": 1}]
    names = ["v1", "v2"]
    
    assert PyBoolNet.temporal_logic.exists_finally_one_of_subspaces(names, subspaces) == "EF(!v1&!v2 | v1&v2)"


def test_ef_unsteady():
    names = ["v1", "v2", "v3"]
    
    assert PyBoolNet.temporal_logic.exists_finally_unsteady_components(names) == "EF(!v1_STEADY) & EF(!v2_STEADY) & EF(!v3_STEADY)"


def test_agef_subspaces():
    subspaces = [{"v1": 0, "v2": 0}, {"v2": 1}]
    names = ["v1", "v2"]
    
    assert PyBoolNet.temporal_logic.all_globally_exists_finally_one_of_sub_spaces(names, subspaces) == "AG(EF(!v1&!v2 | v2))"
