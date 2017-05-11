(* Simulate a random process *)
let mk_distribution arr numSides numTries =
  let l = Array.length arr in
  let arr2 = Array.make l 0 in
  for i = 0 to numTries do
    for idx = 0 to l - 1 do
      (* flip a coin, add the idx with 1/numSides probability  *)
      if Random.int numSides = 0 then
        arr2.(idx) <- arr2.(idx) + arr.(idx)
      else ()
    done
  done;
  arr2
 
let distribution =
  let arr = Array.make 1000 1 in
  let numSides = 6 in
  let numTries = 100000 in
  let l = Array.length arr in
  let arr2 = Array.make l 0 in
  for idx = 0 to l - 1 do
    for i = 0 to numTries do
      (* flip a coin, add the idx with 1/numSides probability  *)
      if Random.int numSides = 0 then
        arr2.(idx) <- arr2.(idx) + arr.(idx)
      else ()
    done
  done;
  arr2
