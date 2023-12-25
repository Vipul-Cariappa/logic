"""Utility/Helper functions"""

from .proposition import (
    CompositePredicateForAll,
    Statement,
    CompositePredicateThereExists,
    Proposition,
)

_unique_number = 0
SUBSCRIPT_NUMBERS = "₀₁₂₃₄₅₆₇₈₉"


def get_unique_number() -> int:
    """generates unique number whenever called

    Returns:
        int: unique number
    """
    global _unique_number
    _unique_number += 1
    return _unique_number


def subscript_number(n: int) -> str:
    """generates string subscript representation of given number

    Args:
        n (int): number

    Returns:
        str: subscript string
    """
    nums = []
    while n:
        nums.append(n % 10)
        n //= 10

    return "".join(SUBSCRIPT_NUMBERS[i] for i in reversed(nums))


def universal_instantiation(
    predicate: CompositePredicateForAll | CompositePredicateThereExists,
) -> Statement:
    """Instantiates the given predicate

    Args:
        predicate (CompositePredicateForAll | CompositePredicateThereExists): predicate to instantiate

    Returns:
        Statement: instantiated statement
    """

    base_variable = predicate.variable
    base_predicate = predicate.predicate
    if Proposition(base_variable) in base_predicate:
        return base_predicate.universal_instantiation(base_variable)
    return predicate


def existential_instantiation(
    predicate: CompositePredicateThereExists | CompositePredicateForAll,
) -> Statement:
    """Instantiates the given predicate

    Args:
        predicate (CompositePredicateThereExists | CompositePredicateForAll): predicate to instantiate

    Returns:
        Statement: instantiated statement
    """

    base_variable = predicate.variable
    base_predicate = predicate.predicate
    if Proposition(base_variable) in base_predicate:
        new_variable = f"{base_variable} {subscript_number(get_unique_number())}"
        return base_predicate.existential_instantiation(base_variable, new_variable)
    return predicate
