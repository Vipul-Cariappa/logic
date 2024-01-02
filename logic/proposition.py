"""All functions and classes related to creation of propositions
and operation between propositions"""

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Any, TypeAlias, Union
from warnings import warn

PropositionT: TypeAlias = "Proposition"
PredicateT: TypeAlias = "Predicate"
CompositePropositionT: TypeAlias = "CompositeProposition"
StatementT: TypeAlias = "Statement"
SpecificBoundVariableT: TypeAlias = "SpecificBoundVariable"
ArbitraryBoundVariableT: TypeAlias = "ArbitraryBoundVariable"


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
    def universal_instantiation(self, variable: str) -> StatementT:
        """Instantiates the given predicate

        Args:
            variable (str): variable to instantiate

        Returns:
            StatementT: instantiated statement
        """

    @abstractmethod
    def existential_instantiation(self, variable: str, new_variable: str) -> StatementT:
        """Instantiates the given predicate

        Args:
            variable (str): variable to instantiate
            new_variable (str): new variable to update with

        Returns:
            StatementT: instantiated statement
        """

    @abstractmethod
    def universal_generalization(self, variable: ArbitraryBoundVariableT) -> StatementT:
        """Generalize the given predicate

        Args:
            variable (ArbitraryBoundVariableT):
              variable to generalize

        Returns:
            StatementT: generalized statement
        """

    @abstractmethod
    def existential_generalization(
        self, variable: Union[ArbitraryBoundVariableT, SpecificBoundVariableT]
    ) -> StatementT:
        """Generalize the given predicate

        Args:
            variable (Union[ArbitraryBoundVariableT, SpecificBoundVariableT]):
              variable to generalize

        Returns:
            StatementT: generalized statement
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

    def universal_instantiation(self, _: str) -> StatementT:
        return self

    def existential_instantiation(self, *_: Any) -> StatementT:
        return self

    def universal_generalization(self, variable: ArbitraryBoundVariableT) -> StatementT:
        return self

    def existential_generalization(
        self, variable: Union[ArbitraryBoundVariableT, SpecificBoundVariableT]
    ) -> StatementT:
        return self

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
    variables: tuple[str | Statement, ...]
    statement: str = ""

    def remove_conditionals(self) -> StatementT:
        return Predicate(
            self.name,
            tuple(
                i if isinstance(i, str) else i.remove_conditionals()
                for i in self.variables
            ),
            self.statement,
        )

    def simplify(self) -> StatementT:
        return self

    def extract(self) -> list[PropositionT]:
        return list(filter(lambda x: isinstance(x, Proposition), self.variables))  # type: ignore

    def universal_instantiation(self, variable: str) -> StatementT:
        updated_variable = ArbitraryBoundVariable(variable)
        result_variables: list[str | StatementT] = []
        for i in self.variables:
            if isinstance(i, str) and i == variable:
                result_variables.append(updated_variable)
            else:
                result_variables.append(i)
        return Predicate(self.name, tuple(result_variables), self.statement)

    def existential_instantiation(self, variable: str, new_variable: str) -> StatementT:
        var, post = new_variable.split(" ")
        updated_variable = SpecificBoundVariable(var, post)
        result_variables: list[str | StatementT] = []
        for i in self.variables:
            if isinstance(i, str) and i == variable:
                result_variables.append(updated_variable)
            else:
                result_variables.append(i)
        return Predicate(self.name, tuple(result_variables), self.statement)

    def universal_generalization(self, variable: ArbitraryBoundVariableT) -> StatementT:
        updated_variable = Proposition(variable.variable)
        result_variables: list[str | StatementT] = []
        for i in self.variables:
            if isinstance(i, ArbitraryBoundVariable) and i == variable:
                result_variables.append(updated_variable)
            else:
                result_variables.append(i)

        return CompositePredicateForAll(
            variable.variable,
            Predicate(self.name, tuple(result_variables), self.statement),
        )

    def existential_generalization(
        self, variable: Union[ArbitraryBoundVariableT, SpecificBoundVariableT]
    ) -> StatementT:
        updated_variable = Proposition(variable.variable)
        result_variables: list[str | StatementT] = []
        for i in self.variables:
            if isinstance(i, ArbitraryBoundVariable) and i == variable:
                result_variables.append(updated_variable)
            elif isinstance(i, SpecificBoundVariable) and i == variable:
                result_variables.append(updated_variable)
            else:
                result_variables.append(i)

        return CompositePredicateThereExists(
            variable.variable,
            Predicate(self.name, tuple(result_variables), self.statement),
        )

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(
                f"Cannot perform in operation of {type(self)} with {type(key)}"
            )

        if isinstance(key, Predicate):
            return self.name == key.name

        for i in self.variables:
            if isinstance(i, str):
                if key == Proposition(i):
                    return True
                continue
            if key == i:
                return True

        return False

    def __call__(self, *args: str | Statement) -> PredicateT:
        if len(args) != len(self.variables):
            raise TypeError("Number of arguments does not match number of variables")

        return Predicate(self.name, args, self.statement)

    def __str__(self) -> str:
        return f"{self.name}(" + ", ".join(str(i) for i in self.variables) + ")"


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

    def universal_instantiation(self, variable: str) -> StatementT:
        return AND(
            self.first.universal_instantiation(variable),
            self.second.universal_instantiation(variable),
        )

    def existential_instantiation(self, variable: str, new_variable: str) -> StatementT:
        return AND(
            self.first.existential_instantiation(variable, new_variable),
            self.second.existential_instantiation(variable, new_variable),
        )

    def universal_generalization(self, variable: ArbitraryBoundVariableT) -> StatementT:
        return AND(
            self.first.universal_generalization(variable),
            self.second.universal_generalization(variable),
        )

    def existential_generalization(
        self, variable: Union[ArbitraryBoundVariableT, SpecificBoundVariableT]
    ) -> StatementT:
        return AND(
            self.first.existential_generalization(variable),
            self.second.existential_generalization(variable),
        )

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

    def universal_instantiation(self, variable: str) -> StatementT:
        return OR(
            self.first.universal_instantiation(variable),
            self.second.universal_instantiation(variable),
        )

    def existential_instantiation(self, variable: str, new_variable: str) -> StatementT:
        return OR(
            self.first.existential_instantiation(variable, new_variable),
            self.second.existential_instantiation(variable, new_variable),
        )

    def universal_generalization(self, variable: ArbitraryBoundVariableT) -> StatementT:
        return OR(
            self.first.universal_generalization(variable),
            self.second.universal_generalization(variable),
        )

    def existential_generalization(
        self, variable: Union[ArbitraryBoundVariableT, SpecificBoundVariableT]
    ) -> StatementT:
        return OR(
            self.first.existential_generalization(variable),
            self.second.existential_generalization(variable),
        )

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

    def universal_instantiation(self, variable: str) -> StatementT:
        return NOT(self.statement.universal_instantiation(variable))

    def existential_instantiation(self, variable: str, new_variable: str) -> StatementT:
        return NOT(self.statement.existential_instantiation(variable, new_variable))

    def universal_generalization(self, variable: ArbitraryBoundVariableT) -> StatementT:
        return NOT(self.statement.universal_generalization(variable))

    def existential_generalization(
        self, variable: Union[ArbitraryBoundVariableT, SpecificBoundVariableT]
    ) -> StatementT:
        return NOT(self.statement.existential_generalization(variable))

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

    def universal_instantiation(self, variable: str) -> StatementT:
        return IMPLY(
            self.assumption.universal_instantiation(variable),
            self.conclusion.universal_instantiation(variable),
        )

    def existential_instantiation(self, variable: str, new_variable: str) -> StatementT:
        return IMPLY(
            self.assumption.existential_instantiation(variable, new_variable),
            self.conclusion.existential_instantiation(variable, new_variable),
        )

    def universal_generalization(self, variable: ArbitraryBoundVariableT) -> StatementT:
        return IMPLY(
            self.assumption.universal_generalization(variable),
            self.conclusion.universal_generalization(variable),
        )

    def existential_generalization(
        self, variable: Union[ArbitraryBoundVariableT, SpecificBoundVariableT]
    ) -> StatementT:
        return IMPLY(
            self.assumption.existential_generalization(variable),
            self.conclusion.existential_generalization(variable),
        )

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

    def universal_instantiation(self, variable: str) -> StatementT:
        return IFF(
            self.assumption.universal_instantiation(variable),
            self.conclusion.universal_instantiation(variable),
        )

    def existential_instantiation(self, variable: str, new_variable: str) -> StatementT:
        return IFF(
            self.assumption.existential_instantiation(variable, new_variable),
            self.conclusion.existential_instantiation(variable, new_variable),
        )

    def universal_generalization(self, variable: ArbitraryBoundVariableT) -> StatementT:
        return IFF(
            self.assumption.universal_generalization(variable),
            self.conclusion.universal_generalization(variable),
        )

    def existential_generalization(
        self, variable: Union[ArbitraryBoundVariableT, SpecificBoundVariableT]
    ) -> StatementT:
        return IFF(
            self.assumption.existential_generalization(variable),
            self.conclusion.existential_generalization(variable),
        )

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
class ArbitraryBoundVariable(Statement):
    """Representation of Arbitrary Variable used in Universal Instantiation
    i.e. to represent x' in ∀x.P(x) to P(x')"""

    variable: str

    def remove_conditionals(self) -> StatementT:
        return self

    def simplify(self) -> StatementT:
        return self

    def extract(self) -> list[PropositionT]:
        return []

    def universal_instantiation(self, _: str) -> StatementT:
        return self

    def existential_instantiation(self, *_: Any) -> StatementT:
        return self

    def universal_generalization(self, variable: ArbitraryBoundVariableT) -> StatementT:
        if self == variable:
            return Proposition(self.variable)
        return self

    def existential_generalization(
        self, variable: Union[ArbitraryBoundVariableT, SpecificBoundVariableT]
    ) -> StatementT:
        if isinstance(self, ArbitraryBoundVariable) and self == variable:
            return Proposition(self.variable)
        return self

    def __contains__(self, key) -> bool:
        if isinstance(key, (ArbitraryBoundVariable, SpecificBoundVariable)):
            return True

        if not isinstance(key, Statement):
            raise TypeError(
                f"Cannot perform in operation of {type(self)} with {type(key)}"
            )

        return False

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, Statement):
            if isinstance(other, ArbitraryBoundVariable):
                return self.variable == other.variable
            return False

        if isinstance(other, str):
            return self.variable == other

        raise TypeError(
            f"Cannot perform equality check of {type(self)} and {type(other)}"
        )

    def __str__(self) -> str:
        return f"{self.variable}'"


@dataclass(frozen=True)
class SpecificBoundVariable(Statement):
    """Representation of Arbitrary Variable used in Universal Instantiation
    i.e. to represent x₁ in ∃x.P(x) to P(x₁)"""

    variable: str
    postfix: str = field(hash=False)

    def remove_conditionals(self) -> StatementT:
        return self

    def simplify(self) -> StatementT:
        return self

    def extract(self) -> list[PropositionT]:
        return []

    def universal_instantiation(self, _: str) -> StatementT:
        return self

    def existential_instantiation(self, *_: Any) -> StatementT:
        return self

    def universal_generalization(self, variable: ArbitraryBoundVariableT) -> StatementT:
        if self == variable:
            return Proposition(self.variable)
        return self

    def existential_generalization(
        self, variable: Union[ArbitraryBoundVariableT, SpecificBoundVariableT]
    ) -> StatementT:
        if isinstance(self, SpecificBoundVariable) and self == variable:
            return Proposition(self.variable)
        return self

    def __contains__(self, key) -> bool:
        if isinstance(key, SpecificBoundVariable):
            return self == key

        if not isinstance(key, (Statement, ArbitraryBoundVariable)):
            raise TypeError(
                f"Cannot perform in operation of {type(self)} with {type(key)}"
            )

        return False

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, Statement):
            if isinstance(other, SpecificBoundVariable):
                return self.variable == other.variable
            return False

        if isinstance(other, str):
            return self.variable == other

        raise TypeError(
            f"Cannot perform equality check of {type(self)} and {type(other)}"
        )

    def __str__(self) -> str:
        return f"{self.variable}{self.postfix}"


@dataclass(frozen=True)
class CompositePredicateForAll(CompositePredicate):
    """Representation of ∀x.P(x)"""

    variable: str
    predicate: Statement

    def universal_instantiation(self, variable: str) -> StatementT:
        return CompositePredicateForAll(
            self.variable, self.predicate.universal_instantiation(variable)
        )

    def existential_instantiation(self, variable: str, new_variable: str) -> StatementT:
        return CompositePredicateForAll(
            self.variable,
            self.predicate.existential_instantiation(variable, new_variable),
        )

    def universal_generalization(self, variable: ArbitraryBoundVariableT) -> StatementT:
        return CompositePredicateForAll(
            self.variable, self.predicate.universal_generalization(variable)
        )

    def existential_generalization(
        self, variable: Union[ArbitraryBoundVariableT, SpecificBoundVariableT]
    ) -> StatementT:
        return CompositePredicateForAll(
            self.variable,
            self.predicate.existential_generalization(variable),
        )

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(
                f"Cannot perform in operation of {type(self)} with {type(key)}"
            )

        return key in self.predicate

    def __str__(self) -> str:
        return f"∀{self.variable}.{str(self.predicate)}"


@dataclass(frozen=True)
class CompositePredicateThereExists(CompositePredicate):
    """Representation of ∃x.P(x)"""

    variable: str
    predicate: Statement

    def universal_instantiation(self, variable: str) -> StatementT:
        return CompositePredicateThereExists(
            self.variable, self.predicate.universal_instantiation(variable)
        )

    def existential_instantiation(self, variable: str, new_variable: str) -> StatementT:
        return CompositePredicateThereExists(
            self.variable,
            self.predicate.existential_instantiation(variable, new_variable),
        )

    def universal_generalization(self, variable: ArbitraryBoundVariableT) -> StatementT:
        return CompositePredicateThereExists(
            self.variable, self.predicate.universal_generalization(variable)
        )

    def existential_generalization(
        self, variable: Union[ArbitraryBoundVariableT, SpecificBoundVariableT]
    ) -> StatementT:
        return CompositePredicateThereExists(
            self.variable,
            self.predicate.existential_generalization(variable),
        )

    def __contains__(self, key: Any) -> bool:
        if not isinstance(key, Statement):
            raise TypeError(
                f"Cannot perform in operation of {type(self)} with {type(key)}"
            )

        return key in self.predicate

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
