# 0164: Plain sentences for a vector that may be too long and for a companion lemma, one line per failure, and two refusals

Date: 2026-10-19. Status: decided. Amends 0068, 0155, 0160 and 0163. The reviews of 0160 and 0163 found these, and the user asked to clear them on 2026-10-19.

## Decision

- A vector that may outgrow the bound of a `Vec` has the sentence `the vector may be too long.` Before, `prove` gave the words of Dafny about a subset constraint. A bound on the length in a requires line or an invariant meets it.
- A local that takes the vector of a call is a sequence, as a local copy is, decision 0160. So a later `push_back` grows it, and the bound applies at the return.
- A failed proof in a lemma of the companion file has the sentence of the same failure in the model. An ensures line gives `the ensures line may not hold on this return.`, and an assert gives `the assert line may not hold.` A function or a predicate of the companion file keeps the words of Dafny, decision 0084.
- A failure that breaks a line of the companion file shows that line under it, as `The contract line:`. That holds for an ensures line of a lemma and for a requires line of a lemma at an `apply`.
- `prove` prints one line for each place, sentence and set of contract lines that it shows. A comparator that breaks two clauses of a strict weak order gives one line, not two. Two ensures lines that fail at the same return still give two lines, because they show different contract lines, decision 0155.
- The translator refuses a vector by reference of a struct that holds a sequence, as decision 0163 says. A read-only vector of such a struct stays a parameter of 0064, as 0076 allows. Nothing writes it, so its value stays the same. The sentence of the refusal is now `a struct that holds a sequence is in the subset only as a parameter that the function does not write.` The old sentence said "only as a parameter", and the refused thing can be a parameter.
- The translator refuses a local vector that copies a name that is not in scope, such as `std::vector<int32_t> x = x;`. The sentence is the one of 0160: `a local vector has a rule only as a copy of a vector in scope.`

## Why

Each sentence that a bot reads names the fault in the words of the policy, decision 0155. The words of Dafny name a type of the model, and a bot cannot act on them. The two refusals make the code meet what 0160 and 0163 already say. The review found that two failures in the companion file printed as one line. A bot then fixes one and sees the other only on the next run. With the line of the companion file under each failure, the two lines are different again.
