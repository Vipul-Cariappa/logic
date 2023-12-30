# logic

Logic is a predicate logic simulator. It can be used to create automated proof.

## Installation

Install using pip with the git url

```bash
pip install py-logic
```

## Example Usage

```python
from logic import Proposition, IMPLY, prove


# Creating propositional variables
a = Proposition("a")
b = Proposition("b")

assumptions = [
  IMPLY(a, b), # if a then b
  ~b,          # not b
]

conclusion = ~a # not a

# generating proof
proof, truth = prove(assumptions, conclusion)

print(proof)
```

Output

Using Modus Tollens the above conclusion can be proved:

```text
               ¬ (a)                Modus Tollens {((a) → (b)), ¬ (b)}     
```

---

This is question from Discrete Mathematics and Its Applications 7th Edition by Kenneth H. Rosen.

*If Superman were able and willing to prevent evil,
he would do so. If Superman were unable to prevent
evil, he would be impotent; if he were unwilling
to prevent evil, he would be malevolent. Superman
does not prevent evil. If Superman exists,
he is neither impotent nor malevolent.
Therefore, Superman does not exist.*

**Code to solve the above question**

```python
from logic import Proposition, IMPLY, prove


# Creating propositional variables
a = Proposition("a", "Superman is able to prevent evil")
b = Proposition("b", "Superman is willing to prevent evil")
c = Proposition("c", "Superman is impotent")
d = Proposition("d", "Superman is malevolent")
e = Proposition("e", "Superman prevents evil")
f = Proposition("f", "Superman exists")

# encoding assumptions
assumptions = [
    IMPLY(a & b, e),
    IMPLY(~e, c),
    IMPLY(~b, d),
    ~e,
    IMPLY(f, ~c & ~d),
]

# encoding conclusion
conclusion = ~f

# printing assumptions
print("Assumptions:")
for i in assumptions:
    print(i)

# printing conclusion
print(f"Conclusion: {conclusion}")

# generating proof
proof, truth = prove(assumptions, conclusion)
assert truth == True # checking if it could be proved

# printing proof
print(proof)
```

## TODO
- [ ] Implement support for `ForAll` and `ThereExists`
- [ ] Implement proof verifier, to verify proof given by user
