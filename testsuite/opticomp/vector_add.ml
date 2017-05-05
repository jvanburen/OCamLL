exception A
let vector_add a b =
  let aL = Array.length a in
  let bL = Array.length b in
  let newArr = Array.make aL 0 in
  if aL != bL then raise A
  else for i = 0 to aL - 1 do
         Array.set newArr i ((Array.get a i) + (Array.get b i)) 
       done; newArr

let size = 7000000
let _ = vector_add (Array.make size 1) (Array.make size 2)
