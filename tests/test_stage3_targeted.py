from experiments.stage3_targeted import verify_stage3_local_certificates


def test_stage3_local_certificates_through_11():
    assert verify_stage3_local_certificates(11) == {
        "trees": 434,
        "stars": 9,
        "multi_leaf": 200,
        "single_leaf": 225,
        "paired_sets": 1103,
    }
