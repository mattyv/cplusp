/* /* */ { */
type N = x: int | false witness *
function F(): N
/* /* */ } */
predicate Ok(a: int) ensures false { var n := F(); true }
