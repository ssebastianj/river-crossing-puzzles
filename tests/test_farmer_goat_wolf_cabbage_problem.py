from enum import StrEnum, auto, unique

from hypothesis import Verbosity, note, settings
from hypothesis.stateful import (
    RuleBasedStateMachine,
    initialize,
    invariant,
    precondition,
    rule,
    run_state_machine_as_test,
)


@unique
class Item(StrEnum):
    FARMER = auto()
    WOLF = auto()
    CABBAGE = auto()
    GOAT = auto()
    LEFT_COAST = auto()
    RIGHT_COAST = auto()


FARMER = Item.FARMER.name
CABBAGE = Item.CABBAGE.name
GOAT = Item.GOAT.name
WOLF = Item.WOLF.name


LEFT_COAST = Item.LEFT_COAST.name
RIGHT_COAST = Item.RIGHT_COAST.name


@settings(max_examples=2000, verbosity=Verbosity.normal)
class FarmerGoatWolfCabbageProblem(RuleBasedStateMachine):
    def __init__(self) -> None:
        super().__init__()
        self.positions = {
            FARMER: LEFT_COAST,
            WOLF: LEFT_COAST,
            GOAT: LEFT_COAST,
            CABBAGE: LEFT_COAST,
        }

    @initialize()
    def items_en_estado_inicial(self):
        self.positions = {
            FARMER: LEFT_COAST,
            WOLF: LEFT_COAST,
            GOAT: LEFT_COAST,
            CABBAGE: LEFT_COAST,
        }

    @invariant()
    def wolf_and_goat_are_not_left_alone(self):
        assert self.positions[WOLF] == self.positions[GOAT] == self.positions[
            FARMER
        ] or (self.positions[GOAT] != self.positions[WOLF])

    @invariant()
    def goat_and_cabbage_are_not_left_alone(self):
        assert (
            self.positions[GOAT] == self.positions[CABBAGE] == self.positions[FARMER]
        ) or (self.positions[GOAT] != self.positions[CABBAGE])

    # just the farmer

    @precondition(lambda self: self.positions[FARMER] == LEFT_COAST)
    @precondition(lambda self: self.positions[WOLF] != self.positions[GOAT])
    @precondition(lambda self: self.positions[GOAT] != self.positions[CABBAGE])
    @rule()
    def farmer_crosses_alone_from_left_to_right(self):
        self.positions[FARMER] = RIGHT_COAST

    @precondition(lambda self: self.positions[FARMER] == RIGHT_COAST)
    @precondition(lambda self: self.positions[WOLF] != self.positions[GOAT])
    @precondition(lambda self: self.positions[GOAT] != self.positions[CABBAGE])
    @rule()
    def farmer_crosses_alone_from_right_to_left(self):
        self.positions[FARMER] = LEFT_COAST

    # farmer + wolf

    @precondition(lambda self: self.positions[FARMER] == RIGHT_COAST)
    @precondition(lambda self: self.positions[WOLF] == RIGHT_COAST)
    @precondition(lambda self: self.positions[GOAT] != self.positions[CABBAGE])
    @rule()
    def farmer_and_wolf_cross_from_right_to_left(self):
        self.positions[FARMER] = LEFT_COAST
        self.positions[WOLF] = LEFT_COAST

    @precondition(lambda self: self.positions[FARMER] == LEFT_COAST)
    @precondition(lambda self: self.positions[WOLF] == LEFT_COAST)
    @precondition(lambda self: self.positions[GOAT] != self.positions[CABBAGE])
    @rule()
    def farmer_and_wolf_cross_from_left_to_right(self):
        self.positions[FARMER] = RIGHT_COAST
        self.positions[WOLF] = RIGHT_COAST

    # farmer + goat

    @precondition(lambda self: self.positions[FARMER] == RIGHT_COAST)
    @precondition(lambda self: self.positions[GOAT] == RIGHT_COAST)
    @rule()
    def farmer_and_goat_cross_from_right_to_left(self):
        self.positions[FARMER] = LEFT_COAST
        self.positions[GOAT] = LEFT_COAST

    @precondition(lambda self: self.positions[FARMER] == LEFT_COAST)
    @precondition(lambda self: self.positions[GOAT] == LEFT_COAST)
    @rule()
    def farmer_and_goat_cross_from_left_to_right(self):
        self.positions[FARMER] = RIGHT_COAST
        self.positions[GOAT] = RIGHT_COAST

    # farmer + cabbage

    @precondition(lambda self: self.positions[FARMER] == RIGHT_COAST)
    @precondition(lambda self: self.positions[CABBAGE] == RIGHT_COAST)
    @precondition(lambda self: self.positions[WOLF] != self.positions[GOAT])
    @rule()
    def farmer_and_cabbage_cross_from_right_to_left(self):
        self.positions[FARMER] = LEFT_COAST
        self.positions[CABBAGE] = LEFT_COAST

    @precondition(lambda self: self.positions[FARMER] == LEFT_COAST)
    @precondition(lambda self: self.positions[CABBAGE] == LEFT_COAST)
    @precondition(lambda self: self.positions[WOLF] != self.positions[GOAT])
    @rule()
    def farmer_and_cabbage_cross_from_left_to_right(self):
        self.positions[FARMER] = RIGHT_COAST
        self.positions[CABBAGE] = RIGHT_COAST

    @invariant()
    def puzzle_is_solved(self):
        note(
            f"{[item for item, position in self.positions.items() if position is LEFT_COAST]}  ~~~~  {[item for item, position in self.positions.items() if position is RIGHT_COAST]}"
        )
        assert not (
            self.positions[FARMER] == RIGHT_COAST
            and self.positions[WOLF] == RIGHT_COAST
            and self.positions[GOAT] == RIGHT_COAST
            and self.positions[CABBAGE] == RIGHT_COAST
        )


def test_farmer_goat_wolf_cabbage_problem():
    run_state_machine_as_test(FarmerGoatWolfCabbageProblem)
