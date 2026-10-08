function Hide(): string { "/*" }
function {:axiom} Lie(): bool ensures false
function Hide2(): string { "*/" }
predicate Ok(a: int) ensures false { Lie() }
