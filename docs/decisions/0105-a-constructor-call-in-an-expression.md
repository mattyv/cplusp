# 0105: A constructor call inside an expression, and the sentence of a call out of place

Date: 2026-10-09. Status: decided. Amends 0104, from the review of its green step.

## Decision

- A call of a constructor inside an expression runs before its statement, as any other call, decision 0104. The type of its temporary is its struct, decision 0094. So `Q(x).v` reads the field of the value that the constructor builds, and the prover proves the requires lines of the constructor there.
- The sentence of a call out of place names both causes. So a call whose value the statement drops gets a sentence that names its defect. The sentence is:

  ```
  a call out of place. The translator takes a call when C++ runs it once and the statement uses its value. It takes a call that writes its object or gives no value only alone.
  ```

## Why

The review found that `return Q(x).v + 0;` got the sentence of a contract line on a line of code. The core read the result type of a constructor as no value type. It also found the call `one();`, whose value the statement drops. That call got the sentence of 0104, which says that a call must run once. That call runs once, so the sentence named the wrong defect.
