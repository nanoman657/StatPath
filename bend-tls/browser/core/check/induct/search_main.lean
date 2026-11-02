def main (args : List String) : IO UInt32 := do
  if args.head? == some "trace" then
    let steps := ["connect", "relay", "sock 0 1 open", "page", "discard 0", "sock 0 1 data 1", "page", "sock 0 1 data 1", "page", "page", "connect"]
    for line in Timed.runWith (Timed.TSys.init true 1 1) steps do IO.println line
    return 0
  let depth := (args.head? >>= String.toNat?).getD 6
  let fixed := args.getD 1 "fixed" != "old"
  let (res, n) := Timed.iSearch fixed depth
  IO.println s!"states {n} fixed {fixed} depth {depth}"
  match res with
  | some (name, tr) =>
    IO.println s!"VIOLATED {name} after {tr.length} steps: {tr}"
    return 1
  | none =>
    IO.println "no violation"
    return 0
