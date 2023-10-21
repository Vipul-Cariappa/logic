from typing import Self, Any, TypeAlias
from copy import copy
from abc import ABC, abstractmethod
from warnings import warn
from dataclasses import dataclass

PropositionT: TypeAlias = "Proposition"
CompositePropositionT: TypeAlias = "CompositeProposition"
StatementT: TypeAlias = "Statement"


@dataclass(frozen=True)
class Statement(ABC):
    @abstractmethod
    def remove_conditionals(self) -> StatementT:
        pass

    @abstractmethod
    def simplify(self) -> StatementT:
        pass

    @abstractmethod
    def extract(self) -> list[PropositionT]:
        pass

    @abstractmethod
    def __contains__(self, key: Any) -> bool:
        pass

    def __and__(self, other: Any) -> CompositePropositionT:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot perform logical and of {type(self)} with {type(other)}")
        return CompositePropositionAND(self, other)

    def __or__(self, other: Any) -> CompositePropositionT:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot perform logical or of {type(self)} with {type(other)}")
        return CompositePropositionOR(self, other)

    def __invert__(self) -> CompositePropositionT:
        if isinstance(self, CompositePropositionNOT):
            return copy(self.statement)
        return CompositePropositionNOT(self)

    def __truediv__(self, other: Any) -> CompositePropositionT:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot perform logical imply of {type(self)} with {type(other)}")
        return CompositePropositionCONDITIONAL(self, other)

    def __mod__(self, other: Any) -> CompositePropositionT:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot perform logical bi-conditional of {type(self)} with {type(other)}")
        return CompositePropositionBICONDITIONAL(self, other)


@dataclass(frozen=True)
class Proposition(Statement):
    variable: str
    statement: str = ""

    def remove_conditionals(self) -> StatementT:
        return copy(self)

    def simplify(self) -> StatementT:
        return copy(self)

    def extract(self) -> list[PropositionT]:
        return [self]

    def __str__(self) -> str:
        return self.statement if self.statement else self.variable

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(f"Cannot perform in operation of {type(self)} with {type(key)}")

        if isinstance(key, Proposition):
            return self == key

        return False

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot compare {type(self)} with {type(other)}")

        if isinstance(other, Proposition):
            return self.variable == other.variable

        return False


@dataclass(frozen=True)
class CompositeProposition(Statement):
    def simplify(self) -> StatementT:
        warn("Not Implemented")
        return copy(self)


@dataclass(frozen=True)
class CompositePropositionAND(CompositeProposition):
    first: Statement
    second: Statement

    def remove_conditionals(self) -> StatementT:
        return CompositePropositionAND(self.first.remove_conditionals(), self.second.remove_conditionals())

    def extract(self) -> list[PropositionT]:
        return [*self.first.extract(), *self.second.extract()]

    def __str__(self) -> str:
        return f"({self.first} ∧ {self.second})"

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(f"Cannot perform in operation of {type(self)} with {type(key)}")

        return key in self.first or key in self.second or key == self

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot compare {type(self)} with {type(other)}")

        if isinstance(other, CompositePropositionAND):
            return (self.first == other.first and self.second == other.second) or (
                self.first == other.second and self.second == other.first
            )

        return False


@dataclass(frozen=True)
class CompositePropositionOR(CompositeProposition):
    first: Statement
    second: Statement

    def remove_conditionals(self) -> StatementT:
        return CompositePropositionOR(self.first.remove_conditionals(), self.second.remove_conditionals())

    def extract(self) -> list[PropositionT]:
        return [*self.first.extract(), *self.second.extract()]

    def __str__(self) -> str:
        return f"({self.first} ∨ {self.second})"

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(f"Cannot perform in operation of {type(self)} with {type(key)}")

        return key in self.first or key in self.second or key == self

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot compare {type(self)} with {type(other)}")

        if isinstance(other, CompositePropositionOR):
            return (self.first == other.first and self.second == other.second) or (
                self.first == other.second and self.second == other.first
            )

        return False


@dataclass(frozen=True)
class CompositePropositionNOT(CompositeProposition):
    statement: Statement

    def remove_conditionals(self) -> StatementT:
        return CompositePropositionNOT(self.statement.remove_conditionals())

    def extract(self) -> list[PropositionT]:
        return [*self.statement.extract()]

    def __str__(self) -> str:
        return f"¬ ({self.statement})"

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(f"Cannot perform in operation of {type(self)} with {type(key)}")

        return key in self.statement or key == self

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot compare {type(self)} with {type(other)}")

        if isinstance(other, CompositePropositionNOT):
            # FIXME: this should be part of the proof
            #  By Equivalence of ~(~x) <-> x
            return self.statement == other.statement

        return False


@dataclass(frozen=True)
class CompositePropositionCONDITIONAL(CompositeProposition):
    assumption: Statement
    conclusion: Statement

    def remove_conditionals(self) -> StatementT:
        return ~self.assumption.remove_conditionals() | self.conclusion.remove_conditionals()

    def extract(self) -> list[PropositionT]:
        return [*self.assumption.extract(), *self.conclusion.extract()]

    def __str__(self) -> str:
        return f"(({self.assumption}) → ({self.conclusion}))"

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(f"Cannot perform in operation of {type(self)} with {type(key)}")

        return (
            key in self.assumption
            or key in self.conclusion
            or key == self
            or key == self.assumption
            or key == self.conclusion
        )

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot compare {type(self)} with {type(other)}")

        if isinstance(other, CompositePropositionCONDITIONAL):
            return self.assumption == other.assumption and self.conclusion == other.conclusion

        return False


@dataclass(frozen=True)
class CompositePropositionBICONDITIONAL(CompositeProposition):
    assumption: Statement
    conclusion: Statement

    def remove_conditionals(self) -> StatementT:
        return (self.assumption / self.conclusion).remove_conditionals() & (
            self.conclusion / self.assumption
        ).remove_conditionals()

    def extract(self) -> list[PropositionT]:
        return [*self.assumption.extract(), *self.conclusion.extract()]

    def __str__(self) -> str:
        return f"(({self.assumption}) ↔ ({self.conclusion}))"

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(f"Cannot perform in operation of {type(self)} with {type(key)}")

        return (
            key in self.assumption
            or key in self.conclusion
            or key == self
            or key == self.assumption
            or key == self.conclusion
        )

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot compare {type(self)} with {type(other)}")

        if isinstance(other, CompositePropositionBICONDITIONAL):
            return self.assumption == other.assumption and self.conclusion == other.conclusion

        return False
