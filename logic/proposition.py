from typing import Self, Any, TypeAlias
from copy import copy
from abc import ABC, abstractmethod
from warnings import warn

PropositionT: TypeAlias = "Proposition"
CompositePropositionT: TypeAlias = "CompositeProposition"
StatementT: TypeAlias = "Statement"


class Statement(ABC):
    @abstractmethod
    def remove_conditionals(self) -> StatementT:
        pass

    @abstractmethod
    def simplify(self) -> StatementT:
        pass

    def __and__(self, other: Any) -> CompositePropositionT:
        if not isinstance(other, Statement):
            raise TypeError(
                f"Cannot perform logical and of {type(self)} with {type(other)}"
            )
        return CompositePropositionAND(self, other)

    def __or__(self, other: Any) -> CompositePropositionT:
        if not isinstance(other, Statement):
            raise TypeError(
                f"Cannot perform logical or of {type(self)} with {type(other)}"
            )
        return CompositePropositionOR(self, other)

    def __invert__(self) -> CompositePropositionT:
        return CompositePropositionNOT(self)

    def __truediv__(self, other: Any) -> CompositePropositionT:
        if not isinstance(other, Statement):
            raise TypeError(
                f"Cannot perform logical imply of {type(self)} with {type(other)}"
            )
        return CompositePropositionCONDITIONAL(self, other)

    def __mod__(self, other: Any) -> CompositePropositionT:
        if not isinstance(other, Statement):
            raise TypeError(
                f"Cannot perform logical bi-conditional of {type(self)} with {type(other)}"
            )
        return CompositePropositionBICONDITIONAL(self, other)


class Proposition(Statement):
    def __init__(self, variable: str, statement: None | str = None) -> None:
        self.variable = variable
        self.statement = statement if statement else variable

    def remove_conditionals(self) -> StatementT:
        return copy(self)

    def simplify(self) -> StatementT:
        return copy(self)

    def __str__(self) -> str:
        return self.statement

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot compare {type(self)} with {type(other)}")

        if isinstance(other, Proposition):
            return self.variable == other.variable

        return False


class CompositeProposition(Statement):
    def simplify(self) -> StatementT:
        warn("Not Implemented")
        return copy(self)


class CompositePropositionAND(CompositeProposition):
    def __init__(self, first: Statement, second: Statement) -> None:
        self.first = first
        self.second = second

    def remove_conditionals(self) -> StatementT:
        return CompositePropositionAND(
            self.first.remove_conditionals(), self.second.remove_conditionals()
        )

    def __str__(self) -> str:
        return f"({self.first} ∧ {self.second})"

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot compare {type(self)} with {type(other)}")

        if isinstance(other, CompositePropositionAND):
            return (self.first == other.first and self.second == other.second) or (
                self.first == other.second and self.second == other.first
            )

        return False


class CompositePropositionOR(CompositeProposition):
    def __init__(self, first: Statement, second: Statement) -> None:
        self.first = first
        self.second = second

    def remove_conditionals(self) -> StatementT:
        return CompositePropositionOR(
            self.first.remove_conditionals(), self.second.remove_conditionals()
        )

    def __str__(self) -> str:
        return f"({self.first} ∨ {self.second})"

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot compare {type(self)} with {type(other)}")

        if isinstance(other, CompositePropositionOR):
            return (self.first == other.first and self.second == other.second) or (
                self.first == other.second and self.second == other.first
            )

        return False


class CompositePropositionNOT(CompositeProposition):
    def __init__(self, statement: Statement) -> None:
        self.statement = statement

    def remove_conditionals(self) -> StatementT:
        return CompositePropositionNOT(self.statement.remove_conditionals())

    def __str__(self) -> str:
        return f"¬ ({self.statement})"

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot compare {type(self)} with {type(other)}")

        if isinstance(other, CompositePropositionNOT):
            return self.statement == other.statement

        return False


class CompositePropositionCONDITIONAL(CompositeProposition):
    def __init__(self, assumption: Statement, conclusion: Statement) -> None:
        self.assumption = assumption
        self.conclusion = conclusion

    def remove_conditionals(self) -> StatementT:
        return (
            ~self.assumption.remove_conditionals()
            | self.conclusion.remove_conditionals()
        )

    def __str__(self) -> str:
        return f"(({self.assumption}) → ({self.conclusion}))"

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot compare {type(self)} with {type(other)}")

        if isinstance(other, CompositePropositionCONDITIONAL):
            return (
                self.assumption == other.assumption
                and self.conclusion == other.conclusion
            )

        return False


class CompositePropositionBICONDITIONAL(CompositeProposition):
    def __init__(self, assumption: Statement, conclusion: Statement) -> None:
        self.assumption = assumption
        self.conclusion = conclusion

    def remove_conditionals(self) -> StatementT:
        return (self.assumption / self.conclusion).remove_conditionals() & (
            self.conclusion / self.assumption
        ).remove_conditionals()

    def __str__(self) -> str:
        return f"(({self.assumption}) ↔ ({self.conclusion}))"

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot compare {type(self)} with {type(other)}")

        if isinstance(other, CompositePropositionCONDITIONAL):
            return (
                self.assumption == other.assumption
                and self.conclusion == other.conclusion
            )

        return False
