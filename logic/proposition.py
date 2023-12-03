"""All functions and classes related to creation of propositions
and operation between propositions"""

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Any, TypeAlias
from warnings import warn

PropositionT: TypeAlias = "Proposition"
CompositePropositionT: TypeAlias = "CompositeProposition"
StatementT: TypeAlias = "Statement"


@dataclass(frozen=True)
class Statement(ABC):
    """Base class to represent any type of proposition"""

    @abstractmethod
    def remove_conditionals(self) -> StatementT:
        """Remove all conditions and change it to boolean logic.
            Example: p -> q to  ~p | q

        Returns:
            StatementT: Statement without any conditions or bi-conditionals
        """

    @abstractmethod
    def simplify(self) -> StatementT:
        """Simplifies the given statement

        Returns:
            StatementT: Simplified statement
        """

    @abstractmethod
    def extract(self) -> list[PropositionT]:
        """Extracts individual propositions used in this statement

        Returns:
            list[PropositionT]: List of all individual Propositions
        """

    @abstractmethod
    def __contains__(self, key: Any) -> bool:
        pass

    def __and__(self, other: Any) -> StatementT:
        if not isinstance(other, Statement):
            raise TypeError(
                f"Cannot perform logical and of {type(self)} with {type(other)}"
            )
        return CompositePropositionAND(self, other)

    def __or__(self, other: Any) -> StatementT:
        if not isinstance(other, Statement):
            raise TypeError(
                f"Cannot perform logical or of {type(self)} with {type(other)}"
            )
        return CompositePropositionOR(self, other)

    def __invert__(self) -> StatementT:
        return CompositePropositionNOT(self)


@dataclass(frozen=True)
class Proposition(Statement):
    """Representation of a Proposition"""

    variable: str
    statement: str = ""

    def remove_conditionals(self) -> StatementT:
        return self

    def simplify(self) -> StatementT:
        return self

    def extract(self) -> list[PropositionT]:
        return [self]

    def __str__(self) -> str:
        return self.statement if self.statement else self.variable

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(
                f"Cannot perform in operation of {type(self)} with {type(key)}"
            )

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
class Predicate(Statement):
    """Representation of a Predicate"""

    name: str
    variables: tuple[str, ...]
    statement: str = ""

    def remove_conditionals(self) -> StatementT:
        return self

    def simplify(self) -> StatementT:
        return self

    def extract(self) -> list[PropositionT]:
        return []

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(
                f"Cannot perform in operation of {type(self)} with {type(key)}"
            )

        if isinstance(key, Predicate):
            return self == key

        return False

    def __str__(self) -> str:
        return f"{self.name}(" + ", ".join(self.variables) + ")"


@dataclass(frozen=True)
class CompositeProposition(Statement):
    """Representation of a Proposition constructed with some operator"""

    def simplify(self) -> StatementT:
        warn("Not Implemented")
        return self


@dataclass(frozen=True)
class CompositePropositionAND(CompositeProposition):
    """Representation of p & q"""

    first: Statement
    second: Statement

    def remove_conditionals(self) -> StatementT:
        return CompositePropositionAND(
            self.first.remove_conditionals(), self.second.remove_conditionals()
        )

    def extract(self) -> list[PropositionT]:
        return [*self.first.extract(), *self.second.extract()]

    def __str__(self) -> str:
        return f"({self.first} ∧ {self.second})"

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(
                f"Cannot perform in operation of {type(self)} with {type(key)}"
            )

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
    """Representation of p | q"""

    first: Statement
    second: Statement

    def remove_conditionals(self) -> StatementT:
        return CompositePropositionOR(
            self.first.remove_conditionals(), self.second.remove_conditionals()
        )

    def extract(self) -> list[PropositionT]:
        return [*self.first.extract(), *self.second.extract()]

    def __str__(self) -> str:
        return f"({self.first} ∨ {self.second})"

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(
                f"Cannot perform in operation of {type(self)} with {type(key)}"
            )

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
    """Representation of ~p"""

    statement: Statement

    def remove_conditionals(self) -> StatementT:
        return CompositePropositionNOT(self.statement.remove_conditionals())

    def extract(self) -> list[PropositionT]:
        return [*self.statement.extract()]

    def __str__(self) -> str:
        return f"¬ ({self.statement})"

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(
                f"Cannot perform in operation of {type(self)} with {type(key)}"
            )

        return key in self.statement or key == self

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Statement):
            raise TypeError(f"Cannot compare {type(self)} with {type(other)}")

        if isinstance(other, CompositePropositionNOT):
            return self.statement == other.statement

        return False


@dataclass(frozen=True)
class CompositePropositionCONDITIONAL(CompositeProposition):
    """Representation of p -> q"""

    assumption: Statement
    conclusion: Statement

    def remove_conditionals(self) -> StatementT:
        return (
            ~self.assumption.remove_conditionals()
            | self.conclusion.remove_conditionals()
        )

    def extract(self) -> list[PropositionT]:
        return [*self.assumption.extract(), *self.conclusion.extract()]

    def __str__(self) -> str:
        return f"(({self.assumption}) → ({self.conclusion}))"

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(
                f"Cannot perform in operation of {type(self)} with {type(key)}"
            )

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
            return (
                self.assumption == other.assumption
                and self.conclusion == other.conclusion
            )

        return False


@dataclass(frozen=True)
class CompositePropositionBICONDITIONAL(CompositeProposition):
    """Representation of p <-> q"""

    assumption: Statement
    conclusion: Statement

    def remove_conditionals(self) -> StatementT:
        return (IMPLY(self.assumption, self.conclusion)).remove_conditionals() & (
            IMPLY(self.conclusion, self.assumption)
        ).remove_conditionals()

    def extract(self) -> list[PropositionT]:
        return [*self.assumption.extract(), *self.conclusion.extract()]

    def __str__(self) -> str:
        return f"(({self.assumption}) ↔ ({self.conclusion}))"

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(
                f"Cannot perform in operation of {type(self)} with {type(key)}"
            )

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
            return (
                self.assumption == other.assumption
                and self.conclusion == other.conclusion
            )

        return False


@dataclass(frozen=True)
class CompositePredicate(Statement):
    """Representation of a Predicate constructed with some operator"""

    def remove_conditionals(self) -> StatementT:
        return self

    def simplify(self) -> StatementT:
        return self

    def extract(self) -> list[PropositionT]:
        return []


@dataclass(frozen=True)
class CompositePredicateForAll(CompositePredicate):
    """Representation of ∀x.P(x)"""

    variable: str
    predicate: Predicate | CompositePredicate

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(
                f"Cannot perform in operation of {type(self)} with {type(key)}"
            )

        if isinstance(key, CompositePredicateForAll):
            return self == key

        return False

    def __str__(self) -> str:
        return f"∀{self.variable}.{str(self.predicate)}"


@dataclass(frozen=True)
class CompositePredicateThereExists(CompositePredicate):
    """Representation of ∃x.P(x)"""

    variable: str
    predicate: Predicate | CompositePredicate

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(
                f"Cannot perform in operation of {type(self)} with {type(key)}"
            )

        if isinstance(key, CompositePredicateForAll):
            return self == key

        return False

    def __str__(self) -> str:
        return f"∃{self.variable}.{str(self.predicate)}"


def AND(
    first: Statement, second: Statement, *others: Statement
) -> CompositePropositionAND:
    """Constructs Composite Proportions with & as the operators between them

    Args:
        first (Statement): First proposition
        second (Statement): Second proposition
        others (*Statement): Any length of other propositions

    Returns:
        CompositePropositionAND: Proposition and(ed) with all given propositions
    """
    if len(others) == 0:
        return CompositePropositionAND(first, second)

    return CompositePropositionAND(first, AND(second, *others))


def OR(
    first: Statement, second: Statement, *others: Statement
) -> CompositePropositionOR:
    """Constructs Composite Proportions with | as the operators between them

    Args:
        first (Statement): First proposition
        second (Statement): Second proposition
        others (*Statement): Any length of other propositions

    Returns:
        CompositePropositionAND: Proposition or(ed) with all given propositions
    """
    if len(others) == 0:
        return CompositePropositionOR(first, second)

    return CompositePropositionOR(first, OR(second, *others))


def NOT(statement: Statement) -> CompositePropositionNOT:
    """Constructs Composite Proposition that is ~ of statement

    Args:
        statement (Statement): Proposition to negate

    Returns:
        CompositePropositionNOT: Negated Proposition
    """
    return CompositePropositionNOT(statement)


def IMPLY(
    assumption: Statement, conclusion: Statement
) -> CompositePropositionCONDITIONAL:
    """Construct Composite Proposition with -> as the operator between them

    Args:
        assumption (Statement): The assumption proposition
        conclusion (Statement): The conclusion proposition

    Returns:
        CompositePropositionCONDITIONAL: Conditional Proposition
    """
    return CompositePropositionCONDITIONAL(assumption, conclusion)


def IFF(
    assumption: Statement, conclusion: Statement
) -> CompositePropositionBICONDITIONAL:
    """Construct Composite Proposition with <-> as the operator between them.
        i.e. constructs if and only if

    Args:
        assumption (Statement): The assumption proposition
        conclusion (Statement): The conclusion proposition

    Returns:
        CompositePropositionBICONDITIONAL: Bi-Conditional Proposition
    """
    return CompositePropositionBICONDITIONAL(assumption, conclusion)


def FORALL(
    variable: str, predicate: Predicate | CompositePredicate
) -> CompositePredicateForAll:
    """Construct Composite Predicate with ∀ as the operator
    i.e. for all

    Args:
        variable (str): variable name should match with the predicate's argument
        predicate (Predicate | CompositePredicate): predicate to apply on

    Returns:
        CompositePredicate: For All Predicate
    """
    return CompositePredicateForAll(variable, predicate)


def THEREEXISTS(
    variable: str, predicate: Predicate | CompositePredicate
) -> CompositePredicateThereExists:
    """Construct Composite Predicate with ∃ as the operator
    i.e. there exists

    Args:
        variable (str): variable name should match with the predicate's argument
        predicate (Predicate | CompositePredicate): predicate to apply on

    Returns:
        CompositePredicate: There Exists Predicate
    """
    return CompositePredicateThereExists(variable, predicate)
