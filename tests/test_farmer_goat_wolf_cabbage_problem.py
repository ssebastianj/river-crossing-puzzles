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


@unique
class Terrain(StrEnum):
    LEFT_COAST = auto()
    RIGHT_COAST = auto()


@settings(max_examples=2000, verbosity=Verbosity.normal)
class FarmerGoatWolfCabbageProblem(RuleBasedStateMachine):
    def __init__(self) -> None:
        super().__init__()

    @initialize()
    def items_start_at_the_left_coast(self) -> None:
        self.positions: dict[Item, Terrain] = {
            Item.FARMER: Terrain.LEFT_COAST,
            Item.WOLF: Terrain.LEFT_COAST,
            Item.GOAT: Terrain.LEFT_COAST,
            Item.CABBAGE: Terrain.LEFT_COAST,
        }

    @invariant()
    def wolf_and_goat_are_not_left_alone(self):
        assert self.positions[Item.WOLF] is self.positions[Item.GOAT] is self.positions[
            Item.FARMER
        ] or (self.positions[Item.GOAT] is not self.positions[Item.WOLF])

    @invariant()
    def goat_and_cabbage_are_not_left_alone(self):
        assert (
            self.positions[Item.GOAT]
            is self.positions[Item.CABBAGE]
            is self.positions[Item.FARMER]
        ) or (self.positions[Item.GOAT] is not self.positions[Item.CABBAGE])

    # just the farmer

    @precondition(lambda self: self.positions[Item.FARMER] is Terrain.LEFT_COAST)
    @precondition(
        lambda self: self.positions[Item.WOLF] is not self.positions[Item.GOAT]
    )
    @precondition(
        lambda self: self.positions[Item.GOAT] is not self.positions[Item.CABBAGE]
    )
    @rule()
    def farmer_crosses_alone_from_left_to_right(self):
        self.positions[Item.FARMER] = Terrain.RIGHT_COAST

    @precondition(lambda self: self.positions[Item.FARMER] is Terrain.RIGHT_COAST)
    @precondition(
        lambda self: self.positions[Item.WOLF] is not self.positions[Item.GOAT]
    )
    @precondition(
        lambda self: self.positions[Item.GOAT] is not self.positions[Item.CABBAGE]
    )
    @rule()
    def farmer_crosses_alone_from_right_to_left(self):
        self.positions[Item.FARMER] = Terrain.LEFT_COAST

    # farmer + wolf

    @precondition(lambda self: self.positions[Item.FARMER] is Terrain.RIGHT_COAST)
    @precondition(lambda self: self.positions[Item.WOLF] is Terrain.RIGHT_COAST)
    @precondition(
        lambda self: self.positions[Item.GOAT] is not self.positions[Item.CABBAGE]
    )
    @rule()
    def farmer_and_wolf_cross_from_right_to_left(self):
        self.positions[Item.FARMER] = Terrain.LEFT_COAST
        self.positions[Item.WOLF] = Terrain.LEFT_COAST

    @precondition(lambda self: self.positions[Item.FARMER] is Terrain.LEFT_COAST)
    @precondition(lambda self: self.positions[Item.WOLF] is Terrain.LEFT_COAST)
    @precondition(
        lambda self: self.positions[Item.GOAT] is not self.positions[Item.CABBAGE]
    )
    @rule()
    def farmer_and_wolf_cross_from_left_to_right(self):
        self.positions[Item.FARMER] = Terrain.RIGHT_COAST
        self.positions[Item.WOLF] = Terrain.RIGHT_COAST

    # farmer + goat

    @precondition(lambda self: self.positions[Item.FARMER] is Terrain.RIGHT_COAST)
    @precondition(lambda self: self.positions[Item.GOAT] is Terrain.RIGHT_COAST)
    @rule()
    def farmer_and_goat_cross_from_right_to_left(self):
        self.positions[Item.FARMER] = Terrain.LEFT_COAST
        self.positions[Item.GOAT] = Terrain.LEFT_COAST

    @precondition(lambda self: self.positions[Item.FARMER] is Terrain.LEFT_COAST)
    @precondition(lambda self: self.positions[Item.GOAT] is Terrain.LEFT_COAST)
    @rule()
    def farmer_and_goat_cross_from_left_to_right(self):
        self.positions[Item.FARMER] = Terrain.RIGHT_COAST
        self.positions[Item.GOAT] = Terrain.RIGHT_COAST

    # farmer + cabbage

    @precondition(lambda self: self.positions[Item.FARMER] is Terrain.RIGHT_COAST)
    @precondition(lambda self: self.positions[Item.CABBAGE] is Terrain.RIGHT_COAST)
    @precondition(
        lambda self: self.positions[Item.WOLF] is not self.positions[Item.GOAT]
    )
    @rule()
    def farmer_and_cabbage_cross_from_right_to_left(self):
        self.positions[Item.FARMER] = Terrain.LEFT_COAST
        self.positions[Item.CABBAGE] = Terrain.LEFT_COAST

    @precondition(lambda self: self.positions[Item.FARMER] is Terrain.LEFT_COAST)
    @precondition(lambda self: self.positions[Item.CABBAGE] is Terrain.LEFT_COAST)
    @precondition(
        lambda self: self.positions[Item.WOLF] is not self.positions[Item.GOAT]
    )
    @rule()
    def farmer_and_cabbage_cross_from_left_to_right(self):
        self.positions[Item.FARMER] = Terrain.RIGHT_COAST
        self.positions[Item.CABBAGE] = Terrain.RIGHT_COAST

    @invariant()
    def puzzle_is_not_solved(self):
        note(
            f"{[item.name for item, position in self.positions.items() if position is Terrain.LEFT_COAST]}  ~~~~  {[item.name for item, position in self.positions.items() if position is Terrain.RIGHT_COAST]}"
        )
        assert not (
            self.positions[Item.FARMER] is Terrain.RIGHT_COAST
            and self.positions[Item.WOLF] is Terrain.RIGHT_COAST
            and self.positions[Item.GOAT] is Terrain.RIGHT_COAST
            and self.positions[Item.CABBAGE] is Terrain.RIGHT_COAST
        )


def test_farmer_goat_wolf_cabbage_problem():
    run_state_machine_as_test(FarmerGoatWolfCabbageProblem)
