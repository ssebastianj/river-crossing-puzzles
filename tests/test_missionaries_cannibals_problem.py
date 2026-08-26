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
class Terrain(StrEnum):
    LEFT_BANK = auto()
    RIGHT_BANK = auto()


@unique
class MacGuffin(StrEnum):
    CANOE = auto()


@unique
class Missionary(StrEnum):
    MISSIONARY_A = auto()
    MISSIONARY_B = auto()
    MISSIONARY_C = auto()


@unique
class Cannibal(StrEnum):
    CANNIBAL_A = auto()
    CANNIBAL_B = auto()
    CANNIBAL_C = auto()


def cross_to_right_bank_is_valid(
    self,
    *,
    crossers: list[Missionary | Cannibal],
) -> bool:
    number_missionaries_crossing: int = sum(
        1 for item in crossers if item in Missionary
    )
    number_cannibals_crossing: int = sum(1 for item in crossers if item in Cannibal)

    number_missionaries_remaining_on_righ_bank: int = sum(
        (
            1
            for item, pos in self.positions.items()
            if item in Missionary and pos == Terrain.RIGHT_BANK
        ),
        start=number_missionaries_crossing,
    )
    number_cannibals_remaining_on_right_bank: int = sum(
        (
            1
            for item, pos in self.positions.items()
            if item in Cannibal and pos == Terrain.RIGHT_BANK
        ),
        start=number_cannibals_crossing,
    )

    number_missionaries_remaining_on_left_bank: int = sum(
        (
            1
            for item, pos in self.positions.items()
            if item in Missionary and pos == Terrain.LEFT_BANK
        ),
        start=number_missionaries_crossing * -1,
    )
    number_cannibals_remaining_on_left_bank: int = sum(
        (
            1
            for item, pos in self.positions.items()
            if item in Cannibal and pos == Terrain.LEFT_BANK
        ),
        start=number_cannibals_crossing * -1,
    )

    right_bank_is_valid: bool = (
        not number_missionaries_remaining_on_righ_bank
        or not number_cannibals_remaining_on_right_bank
    ) or (
        number_missionaries_remaining_on_righ_bank
        >= number_cannibals_remaining_on_right_bank
    )

    left_bank_is_valid: bool = (
        not number_missionaries_remaining_on_left_bank
        or not number_cannibals_remaining_on_left_bank
    ) or (
        number_missionaries_remaining_on_left_bank
        >= number_cannibals_remaining_on_left_bank
    )

    return right_bank_is_valid and left_bank_is_valid


def cross_to_left_bank_is_valid(
    self,
    *,
    crossers: list[Missionary | Cannibal],
) -> bool:
    number_missionaries_crossing: int = sum(
        1 for item in crossers if item in Missionary
    )
    number_cannibals_crossing: int = sum(1 for item in crossers if item in Cannibal)

    number_missionaries_remaining_on_righ_bank: int = sum(
        (
            1
            for item, pos in self.positions.items()
            if item in Missionary and pos == Terrain.RIGHT_BANK
        ),
        start=number_missionaries_crossing * -1,
    )
    number_cannibals_remaining_on_right_bank: int = sum(
        (
            1
            for item, pos in self.positions.items()
            if item in Cannibal and pos == Terrain.RIGHT_BANK
        ),
        start=number_cannibals_crossing * -1,
    )

    number_missionaries_remaining_on_left_bank: int = sum(
        (
            1
            for item, pos in self.positions.items()
            if item in Missionary and pos == Terrain.LEFT_BANK
        ),
        start=number_missionaries_crossing,
    )
    number_cannibals_remaining_on_left_bank: int = sum(
        (
            1
            for item, pos in self.positions.items()
            if item in Cannibal and pos == Terrain.LEFT_BANK
        ),
        start=number_cannibals_crossing,
    )

    right_bank_is_valid: bool = (
        not number_missionaries_remaining_on_righ_bank
        or not number_cannibals_remaining_on_right_bank
    ) or (
        number_missionaries_remaining_on_righ_bank
        >= number_cannibals_remaining_on_right_bank
    )

    left_bank_is_valid: bool = (
        not number_missionaries_remaining_on_left_bank
        or not number_cannibals_remaining_on_left_bank
    ) or (
        number_missionaries_remaining_on_left_bank
        >= number_cannibals_remaining_on_left_bank
    )

    return right_bank_is_valid and left_bank_is_valid


@settings(max_examples=2500, verbosity=Verbosity.normal)
class MissionariesCannibalsProblem(RuleBasedStateMachine):
    def __init__(self) -> None:
        super().__init__()
        self.positions: dict[Missionary | Cannibal | MacGuffin, Terrain] = {}

    @initialize()
    def items_are_at_the_starting_bank(self):
        self.positions = {
            Missionary.MISSIONARY_A: Terrain.LEFT_BANK,
            Missionary.MISSIONARY_B: Terrain.LEFT_BANK,
            Missionary.MISSIONARY_C: Terrain.LEFT_BANK,
            Cannibal.CANNIBAL_A: Terrain.LEFT_BANK,
            Cannibal.CANNIBAL_B: Terrain.LEFT_BANK,
            Cannibal.CANNIBAL_C: Terrain.LEFT_BANK,
            MacGuffin.CANOE: Terrain.LEFT_BANK,
        }

    @invariant()
    def number_of_items_in_the_world(self):
        number_items_on_left_bank = sum(
            1 for _, position in self.positions.items() if position == Terrain.LEFT_BANK
        )
        number_items_on_right_bank = sum(
            1
            for _, position in self.positions.items()
            if position == Terrain.RIGHT_BANK
        )
        assert number_items_on_left_bank + number_items_on_right_bank == 7

    @invariant()
    def cannibals_do_not_outnumber_missionaries_on_left_bank(self):
        number_cannibals_on_left_bank = sum(
            1
            for item, position in self.positions.items()
            if item in Cannibal and position == Terrain.LEFT_BANK
        )
        number_missionaries_on_left_bank = sum(
            1
            for item, position in self.positions.items()
            if item in Missionary and position == Terrain.LEFT_BANK
        )
        if number_missionaries_on_left_bank:
            assert number_cannibals_on_left_bank <= number_missionaries_on_left_bank

    @invariant()
    def cannibals_do_not_outnumber_missionaries_on_right_bank(self):
        number_cannibals_on_right_bank = sum(
            1
            for item, position in self.positions.items()
            if item in Cannibal and position == Terrain.RIGHT_BANK
        )
        number_missionaries_on_right_bank = sum(
            1
            for item, position in self.positions.items()
            if item in Missionary and position == Terrain.RIGHT_BANK
        )
        if number_missionaries_on_right_bank:
            assert number_cannibals_on_right_bank <= number_missionaries_on_right_bank

    @invariant()
    def problem_is_not_solved(self):
        items_on_left_bank = [
            str(item)
            for item, position in self.positions.items()
            if position == Terrain.LEFT_BANK
        ]
        items_on_right_bank = [
            str(item)
            for item, position in self.positions.items()
            if position == Terrain.RIGHT_BANK
        ]
        note(f"{items_on_left_bank}  ~~~~  {items_on_right_bank}")

        assert self.positions != {
            Missionary.MISSIONARY_A: Terrain.RIGHT_BANK,
            Missionary.MISSIONARY_B: Terrain.RIGHT_BANK,
            Missionary.MISSIONARY_C: Terrain.RIGHT_BANK,
            Cannibal.CANNIBAL_A: Terrain.RIGHT_BANK,
            Cannibal.CANNIBAL_B: Terrain.RIGHT_BANK,
            Cannibal.CANNIBAL_C: Terrain.RIGHT_BANK,
            MacGuffin.CANOE: Terrain.RIGHT_BANK,
        }

    # cannibals

    ## cannibal A

    @precondition(
        lambda self: self.positions[Cannibal.CANNIBAL_A]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(self, crossers=[Cannibal.CANNIBAL_A])
    )
    @rule()
    def cannibal_a_crosses_from_left_to_right(self):
        self.positions[Cannibal.CANNIBAL_A] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Cannibal.CANNIBAL_A]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(self, crossers=[Cannibal.CANNIBAL_A])
    )
    @rule()
    def cannibal_a_crosses_from_right_to_left(self):
        self.positions[Cannibal.CANNIBAL_A] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    ## cannibal B

    @precondition(
        lambda self: self.positions[Cannibal.CANNIBAL_B]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(self, crossers=[Cannibal.CANNIBAL_B])
    )
    @rule()
    def cannibal_b_crosses_from_left_to_right(self):
        self.positions[Cannibal.CANNIBAL_B] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Cannibal.CANNIBAL_B]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(self, crossers=[Cannibal.CANNIBAL_B])
    )
    @rule()
    def cannibal_b_crosses_from_right_to_left(self):
        self.positions[Cannibal.CANNIBAL_B] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    ## cannibal C

    @precondition(
        lambda self: self.positions[Cannibal.CANNIBAL_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(self, crossers=[Cannibal.CANNIBAL_C])
    )
    @rule()
    def cannibal_c_crosses_from_left_to_right(self):
        self.positions[Cannibal.CANNIBAL_C] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Cannibal.CANNIBAL_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(self, crossers=[Cannibal.CANNIBAL_C])
    )
    @rule()
    def cannibal_c_crosses_from_right_to_left(self):
        self.positions[Cannibal.CANNIBAL_C] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    # cannibals A + B

    @precondition(
        lambda self: self.positions[Cannibal.CANNIBAL_A]
        == self.positions[Cannibal.CANNIBAL_B]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Cannibal.CANNIBAL_A, Cannibal.CANNIBAL_B]
        )
    )
    @rule()
    def cannibals_a_b_cross_from_left_to_right(self):
        self.positions[Cannibal.CANNIBAL_A] = Terrain.RIGHT_BANK
        self.positions[Cannibal.CANNIBAL_B] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Cannibal.CANNIBAL_A]
        == self.positions[Cannibal.CANNIBAL_B]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Cannibal.CANNIBAL_A, Cannibal.CANNIBAL_B]
        )
    )
    @rule()
    def cannibals_a_b_cross_from_right_to_left(self):
        self.positions[Cannibal.CANNIBAL_A] = Terrain.LEFT_BANK
        self.positions[Cannibal.CANNIBAL_B] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    # cannibals A + C

    @precondition(
        lambda self: self.positions[Cannibal.CANNIBAL_A]
        == self.positions[Cannibal.CANNIBAL_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Cannibal.CANNIBAL_A, Cannibal.CANNIBAL_C]
        )
    )
    @rule()
    def cannibals_a_c_cross_from_left_to_right(self):
        self.positions[Cannibal.CANNIBAL_A] = Terrain.RIGHT_BANK
        self.positions[Cannibal.CANNIBAL_C] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Cannibal.CANNIBAL_A]
        == self.positions[Cannibal.CANNIBAL_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Cannibal.CANNIBAL_A, Cannibal.CANNIBAL_C]
        )
    )
    @rule()
    def cannibals_a_c_cross_from_right_to_left(self):
        self.positions[Cannibal.CANNIBAL_A] = Terrain.LEFT_BANK
        self.positions[Cannibal.CANNIBAL_C] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    # cannibals B + C

    @precondition(
        lambda self: self.positions[Cannibal.CANNIBAL_B]
        == self.positions[Cannibal.CANNIBAL_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Cannibal.CANNIBAL_B, Cannibal.CANNIBAL_C]
        )
    )
    @rule()
    def cannibals_b_c_cross_from_left_to_right(self):
        self.positions[Cannibal.CANNIBAL_B] = Terrain.RIGHT_BANK
        self.positions[Cannibal.CANNIBAL_C] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Cannibal.CANNIBAL_B]
        == self.positions[Cannibal.CANNIBAL_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Cannibal.CANNIBAL_B, Cannibal.CANNIBAL_C]
        )
    )
    @rule()
    def cannibals_b_c_cross_from_right_to_left(self):
        self.positions[Cannibal.CANNIBAL_B] = Terrain.LEFT_BANK
        self.positions[Cannibal.CANNIBAL_C] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    # missionaries

    ## missionary A

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_A]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_A]
        )
    )
    @rule()
    def missionary_a_crosses_from_left_to_right(self):
        self.positions[Missionary.MISSIONARY_A] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_A]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_A]
        )
    )
    @rule()
    def missionary_a_crosses_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_A] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    ## missionary B

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_B]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_B]
        )
    )
    @rule()
    def missionary_b_crosses_from_left_to_right(self):
        self.positions[Missionary.MISSIONARY_B] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_B]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_B]
        )
    )
    @rule()
    def missionary_b_crosses_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_B] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    ## missionary C

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_C]
        )
    )
    @rule()
    def missionary_c_crosses_from_left_to_right(self):
        self.positions[Missionary.MISSIONARY_C] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_C]
        )
    )
    @rule()
    def missionary_c_crosses_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_C] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    # missionaries A + B

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_A]
        == self.positions[Missionary.MISSIONARY_B]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_A, Missionary.MISSIONARY_B]
        )
    )
    @rule()
    def missionaries_a_b_cross_from_left_to_right(self):
        self.positions[Missionary.MISSIONARY_A] = Terrain.RIGHT_BANK
        self.positions[Missionary.MISSIONARY_B] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_A]
        == self.positions[Missionary.MISSIONARY_B]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_A, Missionary.MISSIONARY_B]
        )
    )
    @rule()
    def missionaries_a_b_cross_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_A] = Terrain.LEFT_BANK
        self.positions[Missionary.MISSIONARY_B] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    # missionaries A + C

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_A]
        == self.positions[Missionary.MISSIONARY_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_A, Missionary.MISSIONARY_C]
        )
    )
    @rule()
    def missionaries_a_c_cross_from_left_to_right(self):
        self.positions[Missionary.MISSIONARY_A] = Terrain.RIGHT_BANK
        self.positions[Missionary.MISSIONARY_C] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_A]
        == self.positions[Missionary.MISSIONARY_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_A, Missionary.MISSIONARY_C]
        )
    )
    @rule()
    def missionaries_a_c_cross_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_A] = Terrain.LEFT_BANK
        self.positions[Missionary.MISSIONARY_C] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    # missionaries B + C

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_B]
        == self.positions[Missionary.MISSIONARY_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_B, Missionary.MISSIONARY_C]
        )
    )
    @rule()
    def missionaries_b_c_cross_from_left_to_right(self):
        self.positions[Missionary.MISSIONARY_B] = Terrain.RIGHT_BANK
        self.positions[Missionary.MISSIONARY_C] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_B]
        == self.positions[Missionary.MISSIONARY_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_B, Missionary.MISSIONARY_C]
        )
    )
    @rule()
    def missionaries_b_c_cross_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_B] = Terrain.LEFT_BANK
        self.positions[Missionary.MISSIONARY_C] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_A]
        == self.positions[Cannibal.CANNIBAL_A]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_A, Cannibal.CANNIBAL_A]
        )
    )
    @rule()
    def missionary_a_cannibal_a_cross_from_left_to_righ(self):
        self.positions[Missionary.MISSIONARY_A] = Terrain.RIGHT_BANK
        self.positions[Cannibal.CANNIBAL_A] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_A]
        == self.positions[Cannibal.CANNIBAL_B]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_A, Cannibal.CANNIBAL_B]
        )
    )
    @rule()
    def missionary_a_cannibal_b_cross_from_left_to_right(self):
        self.positions[Missionary.MISSIONARY_A] = Terrain.RIGHT_BANK
        self.positions[Cannibal.CANNIBAL_B] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_A]
        == self.positions[Cannibal.CANNIBAL_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_A, Cannibal.CANNIBAL_C]
        )
    )
    @rule()
    def missionary_a_cannibal_c_cross_from_left_to_right(self):
        self.positions[Missionary.MISSIONARY_A] = Terrain.RIGHT_BANK
        self.positions[Cannibal.CANNIBAL_C] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_A]
        == self.positions[Cannibal.CANNIBAL_A]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_A, Cannibal.CANNIBAL_A]
        )
    )
    @rule()
    def missionary_a_cannibal_a_cross_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_A] = Terrain.LEFT_BANK
        self.positions[Cannibal.CANNIBAL_A] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_A]
        == self.positions[Cannibal.CANNIBAL_B]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_A, Cannibal.CANNIBAL_B]
        )
    )
    @rule()
    def missionary_a_cannibal_b_cross_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_A] = Terrain.LEFT_BANK
        self.positions[Cannibal.CANNIBAL_B] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_A]
        == self.positions[Cannibal.CANNIBAL_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_A, Cannibal.CANNIBAL_C]
        )
    )
    @rule()
    def missionary_a_cannibal_c_cross_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_A] = Terrain.LEFT_BANK
        self.positions[Cannibal.CANNIBAL_C] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_B]
        == self.positions[Cannibal.CANNIBAL_A]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_B, Cannibal.CANNIBAL_A]
        )
    )
    @rule()
    def missionary_b_cannibal_a_cross_from_left_to_right(self):
        self.positions[Missionary.MISSIONARY_B] = Terrain.RIGHT_BANK
        self.positions[Cannibal.CANNIBAL_A] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_B]
        == self.positions[Cannibal.CANNIBAL_B]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_B, Cannibal.CANNIBAL_B]
        )
    )
    @rule()
    def missionary_b_cannibal_b_cross_from_left_to_right(self):
        self.positions[Missionary.MISSIONARY_B] = Terrain.RIGHT_BANK
        self.positions[Cannibal.CANNIBAL_B] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_B]
        == self.positions[Cannibal.CANNIBAL_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_B, Cannibal.CANNIBAL_C]
        )
    )
    @rule()
    def missionary_b_cannibal_c_cross_from_left_to_right(self):
        self.positions[Missionary.MISSIONARY_B] = Terrain.RIGHT_BANK
        self.positions[Cannibal.CANNIBAL_C] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_B]
        == self.positions[Cannibal.CANNIBAL_A]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_B, Cannibal.CANNIBAL_A]
        )
    )
    @rule()
    def missionary_b_cannibal_a_cross_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_B] = Terrain.LEFT_BANK
        self.positions[Cannibal.CANNIBAL_A] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_B]
        == self.positions[Cannibal.CANNIBAL_B]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_B, Cannibal.CANNIBAL_B]
        )
    )
    @rule()
    def missionary_b_cannibal_b_cross_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_B] = Terrain.LEFT_BANK
        self.positions[Cannibal.CANNIBAL_B] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_B]
        == self.positions[Cannibal.CANNIBAL_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_B, Cannibal.CANNIBAL_C]
        )
    )
    @rule()
    def missionary_b_cannibal_c_cross_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_B] = Terrain.LEFT_BANK
        self.positions[Cannibal.CANNIBAL_C] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_C]
        == self.positions[Cannibal.CANNIBAL_A]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_C, Cannibal.CANNIBAL_A]
        )
    )
    @rule()
    def missionary_c_cannibal_a_cross_from_left_to_right(self):
        self.positions[Missionary.MISSIONARY_C] = Terrain.RIGHT_BANK
        self.positions[Cannibal.CANNIBAL_A] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_C]
        == self.positions[Cannibal.CANNIBAL_B]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_C, Cannibal.CANNIBAL_B]
        )
    )
    @rule()
    def missionary_c_cannibal_b_cross_from_left_to_right(self):
        self.positions[Missionary.MISSIONARY_C] = Terrain.RIGHT_BANK
        self.positions[Cannibal.CANNIBAL_B] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_C]
        == self.positions[Cannibal.CANNIBAL_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.LEFT_BANK
    )
    @precondition(
        lambda self: cross_to_right_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_C, Cannibal.CANNIBAL_C]
        )
    )
    @rule()
    def missionary_c_cannibal_c_cross_from_left_to_right(self):
        self.positions[Missionary.MISSIONARY_C] = Terrain.RIGHT_BANK
        self.positions[Cannibal.CANNIBAL_C] = Terrain.RIGHT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.RIGHT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_C]
        == self.positions[Cannibal.CANNIBAL_A]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_C, Cannibal.CANNIBAL_A]
        )
    )
    @rule()
    def missionary_c_cannibal_a_cross_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_C] = Terrain.LEFT_BANK
        self.positions[Cannibal.CANNIBAL_A] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_C]
        == self.positions[Cannibal.CANNIBAL_B]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_C, Cannibal.CANNIBAL_B]
        )
    )
    @rule()
    def missionary_c_cannibal_b_cross_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_C] = Terrain.LEFT_BANK
        self.positions[Cannibal.CANNIBAL_B] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK

    @precondition(
        lambda self: self.positions[Missionary.MISSIONARY_C]
        == self.positions[Cannibal.CANNIBAL_C]
        == self.positions[MacGuffin.CANOE]
        == Terrain.RIGHT_BANK
    )
    @precondition(
        lambda self: cross_to_left_bank_is_valid(
            self, crossers=[Missionary.MISSIONARY_C, Cannibal.CANNIBAL_C]
        )
    )
    @rule()
    def missionary_c_cannibal_c_cross_from_right_to_left(self):
        self.positions[Missionary.MISSIONARY_C] = Terrain.LEFT_BANK
        self.positions[Cannibal.CANNIBAL_C] = Terrain.LEFT_BANK
        self.positions[MacGuffin.CANOE] = Terrain.LEFT_BANK


def test_missionaries_cannibals_problem():
    run_state_machine_as_test(MissionariesCannibalsProblem)
