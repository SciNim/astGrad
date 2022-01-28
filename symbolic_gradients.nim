import macros, tables, math

type
  SymbolKind = enum
    skPlus, skMinus, skMul, skDiv, skPower, skInvalid
  SymbolicVariable = object
    n: NimNode # the corresponding nim node
    id: uint64 # unique identifier (mainly for debugging)
    processed: bool # indicates whether derivative has already been computed for this variable
  SymbolicParameter = object
    n: NimNode
    kind: SymbolKind
  SymbolicFunction = object
    n: NimNode
    processed: bool # required?
  Number = distinct


var FunctionTab {.compileTime.} = initTable[string, NimNode]()
var DerivativeTab {.compileTime.} = initTable[string, SymbolicFunction]()
macro defineSupportedFunctions(body: untyped): untyped =
  for fn in body:
    doAssert fn.kind == nnkInfix and fn[0].strVal == "->"
    let fnName = fn[1].strVal
    let fnId = ident(fnName)
    FunctionTab[fnName] = fnId
    DerivativeTab[fnName] = SymbolicFunction(n: fn[2], processed: true)

## NOTE: some of the following functions are not implemented in Nim atm
defineSupportedFunctions:
  sqrt        ->  1.0 / 2.0 / sqrt(x)
  cbrt        ->  1.0 / 3.0 / (cbrt(x)^2.0)
  abs2        ->  1.0 * 2.0 * x
  inv         -> -1.0 * abs2(inv(x))
  log         ->  1.0 / x
  log10       ->  1.0 / x / log(10)
  log2        ->  1.0 / x / log(2.0)
  log1p       ->  1.0 / (x + 1.0)
  exp         ->  exp(x)
  exp2        ->  log(2.0) * exp2(x)
  expm1       ->  exp(x)
  sin         ->  cos(x)
  cos         -> -sin(x)
  tan         ->  (1.0 + (tan(x)^2))
  sec         ->  sec(x) * tan(x)
  csc         -> -csc(x) * cot(x)
  cot         -> -(1.0 + (cot(x)^2))
  sind        ->  Pi / 180.0 * cosd(x)
  cosd        -> -Pi / 180.0 * sind(x)
  tand        ->  Pi / 180.0 * (1.0 + (tand(x)^2))
  secd        ->  Pi / 180.0 * secd(x) * tand(x)
  cscd        -> -Pi / 180.0 * cscd(x) * cotd(x)
  cotd        -> -Pi / 180.0 * (1.0 + (cotd(x)^2))
  arcsin      ->  1.0 / sqrt(1.0 - (x^2))
  arccos      -> -1.0 / sqrt(1.0 - (x^2))
  arctan      ->  1.0 / (1.0 + (x^2))
  arcsec      ->  1.0 / abs(x) / sqrt(x^2 - 1.0)
  arccsc      -> -1.0 / abs(x) / sqrt(x^2 - 1.0)
  arccot      -> -1.0 / (1.0 + (x^2))
  arcsind     ->  180.0 / Pi / sqrt(1.0 - (x^2))
  arccosd     -> -180.0 / Pi / sqrt(1.0 - (x^2))
  arctand     ->  180.0 / Pi / (1.0 + (x^2))
  arcsecd     ->  180.0 / Pi / abs(x) / sqrt(x^2 - 1.0)
  arccscd     -> -180.0 / Pi / abs(x) / sqrt(x^2 - 1.0)
  arccotd     -> -180.0 / Pi / (1.0 + (x^2))
  sinh        ->  cosh(x)
  cosh        ->  sinh(x)
  tanh        ->  sech(x)^2
  sech        -> -tanh(x) * sech(x)
  csch        -> -coth(x) * csch(x)
  coth        -> -(csch(x)^2)
  arcsinh     ->  1.0 / sqrt(x^2 + 1.0)
  arccosh     ->  1.0 / sqrt(x^2 - 1.0)
  arctanh     ->  1.0 / (1.0 - (x^2))
  arcsech     -> -1.0 / x / sqrt(1.0 - (x^2))
  arccsch     -> -1.0 / abs(x) / sqrt(1.0 + (x^2))
  arccoth     ->  1.0 / (1.0 - (x^2))
  deg2rad     ->  Pi / 180.0
  rad2deg     ->  180.0 / Pi
  erf         ->  2.0 * exp(-x*x) / sqrt(Pi)
  erfinv      ->  0.5 * sqrt(Pi) * exp(erfinv(x) * erfinv(x))
  erfc        -> -2.0 * exp(-x*x) / sqrt(Pi)
  erfcinv     -> -0.5 * sqrt(Pi) * exp(erfcinv(x) * erfcinv(x))
  erfi        ->  2.0 * exp(x*x) / sqrt(Pi)
  gamma       ->  digamma(x) * gamma(x)
  lgamma      ->  digamma(x)
  digamma     ->  trigamma(x)
  invdigamma  ->  inv(trigamma(invdigamma(x)))
  trigamma    ->  polygamma(2.0 x)
  airyai      ->  airyaiprime(x)
  airybi      ->  airybiprime(x)
  airyaiprime ->  x * airyai(x)
  airybiprime ->  x * airybi(x)
  besselj0    -> -besselj1(x)
  besselj1    ->  (besselj0(x) - besselj(2.0, x)) / 2.0
  bessely0    -> -bessely1(x)
  bessely1    ->  (bessely0(x) - bessely(2.0, x)) / 2.0
  erfcx       ->  (2.0 * x * erfcx(x) - 2.0 / sqrt(Pi))
  dawson      ->  (1.0 - 2.0 * x * dawson(x))

when false:
  import hashes
  proc hash(x: SymbolicVariable): Hash =
    result = result !& hash(x.n.repr)
    result = result !& hash(x.id)
    result = result !& hash(x.processed)
    result = !$ result

  import sets
  var NodeSet {.compileTime.} = initHashSet[SymbolicVariable]()

var IDCounter {.compileTime.} = 0'u64
template getID(): untyped =
  inc IDCounter
  IDCounter

proc evaluateFunction(fn: SymbolicFunction, arg: SymbolicVariable): SymbolicVariable =
  ## inserts the symbolic variable into the `x` fields and returns a new variable
  ## with the evaluated tree as the node
  var tree = fn.n
  proc insert(n, arg: NimNode): NimNode =
    case n.kind
    of nnkIdent, nnkSym:
      if n.strVal == "x": # this node needs to be replaced
        result = arg
      else:
        result = n
    else:
      if n.len == 0: result = n
      else:
        result = newTree(n.kind)
        for ch in n:
          result.add insert(ch, arg)
  let repl = tree.insert(arg.n)
  result = SymbolicVariable(n: repl, processed: true, id: getID())

proc isNumber(n: NimNode): bool =
  # maybe this: ?
  (n.kind != nnkSym and n.typeKind in {ntyInt .. ntyUInt64}) or
  n.kind in {nnkIntLit .. nnkFloat128Lit}

proc isNumberLit(n: NimNode): bool =
  # maybe this: ?
  n.kind in {nnkIntLit .. nnkFloat128Lit}

proc isNumber(x: SymbolicVariable): bool = x.n.isNumber
proc kind(x: SymbolicVariable): NimNodeKind = x.n.kind
proc `[]`(x: SymbolicVariable, idx: int): SymbolicVariable =
  result = SymbolicVariable(n: x.n[idx], processed: x.processed, id: x.id)

iterator items(x: SymbolicVariable): SymbolicVariable =
  for i in 0 ..< x.n.len:
    yield x[i]

proc add(x: var SymbolicVariable, y: SymbolicVariable) =
  var n = x.n
  n.add y.n
  x = SymbolicVariable(n: n, processed: x.processed, id: x.id)

proc isZero(x: SymbolicVariable): bool = x.n.kind in {nnkFloatLit, nnkFloat64Lit} and x.n.floatVal == 0.0
proc isOne(x: SymbolicVariable): bool = x.n.kind in {nnkFloatLit, nnkFloat64Lit} and x.n.floatVal == 1.0

proc name(fn: SymbolicFunction): string = result = fn.n.strVal

proc toSymbolicVariable(n: NimNode, processed = false): SymbolicVariable =
  #doAssert n.kind in {nnkIdent, nnkSym, nnkIntLit .. nnkFloat128Lit}
  result = SymbolicVariable(n: n, processed: processed, id: getID())

proc symbolicOne(): SymbolicVariable =
  SymbolicVariable(n: newLit(1.0), processed: true, id: getID())

proc symbolicZero(): SymbolicVariable =
  SymbolicVariable(n: newLit(0.0), processed: true, id: getID())

proc symbolicPower(): SymbolicParameter =
  SymbolicParameter(n: ident"^", kind: skPower)

proc `==`(a, b: SymbolicVariable): bool =
  result = a.n == b.n and a.id == b.id

proc isIndep(a, indep: SymbolicVariable): bool =
  ## checks whether `a` is the independent variable.
  result = a.n == indep.n

# not required anymore, we untype the tree
proc san(n: NimNode): NimNode {.inline.} = n
#  case n.kind
#  of nnkStmtListExpr: result = n[1].san
#  of nnkHiddenStdConv, nnkConv: result = n[1].san
#  else: result = n

## TODO: simplify these such that if the second arg is identity element, not included
proc `-`(n: SymbolicVariable): SymbolicVariable =
  result = SymbolicVariable(n: nnkPrefix.newTree(ident"-", n.n.san), processed: true, id: getID())

proc setProcessed(x: SymbolicVariable): SymbolicVariable =
  result = x
  result.n = result.n.san # make sure to sanitize as well
  result.processed = true # most likely already true

proc `+`(x, y: SymbolicVariable): SymbolicVariable =
  if x.isZero: result = y.setProcessed
  elif y.isZero: result = x.setProcessed
  else: result = SymbolicVariable(n: nnkInfix.newTree(ident"+", x.n.san, y.n.san), processed: true, id: getID())

proc litDiff(x, y: NimNode): NimNode =
  if x.kind == y.kind:
    if x.kind == nnkIntLit:
      result = newLit(x.intVal - y.intVal)
    else:
      result = newLit(x.floatVal - y.floatVal)
  else:
    # use float
    template getVal(a: untyped): untyped =
      if a.kind == nnkIntLit: a.intVal.float
      else: a.floatVal
    result = newLit(x.getVal - y.getVal)

proc `-`(x, y: SymbolicVariable): SymbolicVariable =
  if x.isZero: result = -y.setProcessed
  elif y.isZero: result = x.setProcessed
  elif x == y: result = symbolicZero()
  elif x.n.isNumberLit and y.n.isNumberLit: # compute result in place
    result = SymbolicVariable(n: litDiff(x.n, y.n), processed: true, id: getID())
  else: result = SymbolicVariable(n: nnkInfix.newTree(ident"-", x.n.san, y.n.san), processed: true, id: getID())

proc `-`(x: SymbolicVariable, y: SomeNumber): SymbolicVariable =
  result = x - toSymbolicVariable(newLit(y), true)

proc `*`(x, y: SymbolicVariable): SymbolicVariable =
  if x.isOne: result = y.setProcessed
  elif y.isOne: result = x.setProcessed
  elif x.isZero: result = symbolicZero()
  elif y.isZero: result = symbolicZero()
  else:
    result = SymbolicVariable(n: nnkInfix.newTree(ident"*", x.n.san, y.n.san), processed: true, id: getID())

proc `/`(x, y: SymbolicVariable): SymbolicVariable =
  # if x is one, default is shortest already
  if y.isZero: error("Computation contains division by 0!")
  elif x.isZero: result = symbolicZero()
  elif y.isOne: result = x.setProcessed
  elif x == y: result = symbolicOne()
  else: result = SymbolicVariable(n: nnkInfix.newTree(ident"/", x.n.san, y.n.san), processed: true, id: getID())

proc `^`(x, y: SymbolicVariable): SymbolicVariable =
  # if x is one, default is shortest already
  ## XXX: add int literals for powers so that we don't have to force `pow` here!
  if y.isOne: result = x.setProcessed
  elif y.isZero: result = symbolicOne()
  elif x.isZero: result = symbolicZero()
  else: result = SymbolicVariable(n: nnkCall.newTree(ident"pow", x.n.san, y.n.san), processed: true, id: getID())

proc log(x: SymbolicVariable): SymbolicVariable =
  if x.isZero: error("Computation yields log(0) and thus -Inf!")
  else: result = SymbolicVariable(n: nnkCall.newTree(ident"log", x.n.san), processed: true, id: getID())

proc processExpr(arg, wrt: SymbolicVariable): SymbolicVariable

proc differentiate(x, wrt: SymbolicVariable): SymbolicVariable =
  if x.processed:
    result = x
  else:
    result = processExpr(x, wrt)
  doAssert result.processed
  result = result.setProcessed

proc diffPlus(x, y, wrt: SymbolicVariable): SymbolicVariable =
  # compute gradient of `x + y` w.r.t. `wrt`
  result = differentiate(x, wrt) + differentiate(y, wrt)

proc diffMinus(x, y, wrt: SymbolicVariable): SymbolicVariable =
  # compute gradient of `x - y` w.r.t. `wrt`
  result = differentiate(x, wrt) - differentiate(y, wrt)

proc diffMul(x, y, wrt: SymbolicVariable): SymbolicVariable =
  # compute gradient of `x * y` w.r.t. `wrt`
  result = differentiate(x, wrt) * y + x * differentiate(y, wrt)

proc diffDiv(x, y, wrt: SymbolicVariable): SymbolicVariable =
  # compute gradient of `x / y` w.r.t. `wrt`
  result = differentiate(x, wrt) / y + (-x * differentiate(y, wrt) / (y * y))

proc diffPower(x, y, wrt: SymbolicVariable): SymbolicVariable =
  # compute gradient of `x ^ y` w.r.t. `wrt`
  let xp = differentiate(x, wrt)
  let yp = differentiate(y, wrt)
  if xp.isZero and yp.isZero:
    result = symbolicZero()
  elif yp.isZero:
    result = y * xp  * (x ^ (y - 1.0))
  else:
    result = x ^ y * (xp * y / x + yp * log(x))

proc differentiate(op: SymbolicParameter,
                   x, y: SymbolicVariable,
                   wrt: SymbolicVariable): SymbolicVariable =
  case op.kind
  of skPlus: result = diffPlus(x, y, wrt)
  of skMinus: result = diffMinus(x, y, wrt)
  of skMul: result = diffMul(x, y, wrt)
  of skDiv: result = diffDiv(x, y, wrt)
  of skPower: result = diffPower(x, y, wrt)
  of skInvalid: error("Differentiation of `skInvalid` not possible. This is a bug.")

proc differentiate(fn: SymbolicFunction, arg: SymbolicVariable): SymbolicVariable =
  result = evaluateFunction(DerivativeTab[fn.name], arg)

proc parseSymbolicParameter(x: SymbolicVariable): SymbolicParameter =
  doAssert x.kind in {nnkIdent, nnkSym}
  case x.n.strVal
  of "+": result = SymbolicParameter(n: x.n, kind: skPlus)
  of "-": result = SymbolicParameter(n: x.n, kind: skMinus)
  of "*": result = SymbolicParameter(n: x.n, kind: skMul)
  of "/": result = SymbolicParameter(n: x.n, kind: skDiv)
  of "^", "**": result = SymbolicParameter(n: x.n, kind: skPower)
  else: result = SymbolicParameter(n: newEmptyNode(), kind: skInvalid)

proc parseSymbolicFunction(x: SymbolicVariable): SymbolicFunction =
  doAssert x.kind in {nnkIdent, nnkSym}
  result = SymbolicFunction(n: FunctionTab[x.n.strVal])

proc toNimCode(x: SymbolicVariable): NimNode =
  ## Converts the symbolic back into nim code. Just means we return the
  ## NimNode it contains. However, in the future we will add some simple
  ## simplification to act against code explosion.
  x.n

proc handleInfix(arg, wrt: SymbolicVariable): SymbolicVariable =
  ## handle infix nodes by calling the correct differentiation function
  doAssert arg.kind == nnkInfix
  let symbol = parseSymbolicParameter(arg[0])
  result = differentiate(symbol, arg[1], arg[2],
                         wrt)

proc handleCall(arg, wrt: SymbolicVariable): SymbolicVariable =
  ## Essentially handle the chain rule of function calls (and `pow` calls)
  doAssert arg.kind == nnkCall, " is : " & $arg.n.treerepr
  # check if call might be an `infix` symbol. If so, patch up and call infix instead
  if arg[0].parseSymbolicParameter().kind != skInvalid:
    ## XXX: this can go I think. It was due to a bug
    error("invalid")
    doAssert not arg.processed
    var inf = SymbolicVariable(n: nnkInfix.newTree(), processed: arg.processed, id: getID())
    for ch in arg:
      inf.add ch
    result = handleInfix(inf, wrt)
  else:
    # regular function call
    # for now assume single argument functions, i.e. we can evaluate the argument
    # as an expression and there is only one argument
    if arg[0].n.strVal == "pow":
      # power is special case, as it's the only 2 arg function we support so far
      result = differentiate(symbolicPower(), arg[1], arg[2], wrt)
    else:
      let fn = parseSymbolicFunction(arg[0])
      result = differentiate(arg[1], wrt) * differentiate(fn, arg[1]) # chain rule: outer * inner

proc handlePrefix(arg, wrt: SymbolicVariable): SymbolicVariable =
  ## handle prefix, usually `-` or `+`
  expectKind(arg.n, nnkPrefix)
  # parse the prefix symbol
  let fn = parseSymbolicParameter(arg[0])
  case fn.kind
  of skPlus, skMinus:
    # prefix is nothing to be handled via differentiation. Merge it into the element thats after
    result = differentiate(fn, symbolicZero(), # just add / subtract from a zero
                           arg[1],
                           wrt)
  else:
    error("Invalid prefix: " & $fn.n.repr & " from argument: " & $arg.repr)

proc processExpr(arg, wrt: SymbolicVariable): SymbolicVariable =
  ## The heart of the logic. Handles the different nim nodes and performs
  ## the actual differentiation if we are looking at a `nnkSym` or literal
  case arg.kind
  of nnkSym, nnkIdent, nnkIntLit .. nnkFloat128Lit:
    if arg.isIndep(wrt):
      result = symbolicOne()
    else:
      result = symbolicZero()
  of nnkInfix:
    result = handleInfix(arg, wrt)
  of nnkCall:
    result = handleCall(arg, wrt)
  of nnkHiddenStdConv:
    # assume contains literals?
    if arg.isNumber or arg.n.typeKind == ntyRange:
      result = processExpr(arg[1], wrt)
    else:
      error("unsupported: " & $arg.kind & " and value " & $arg.n.treerepr)
  of nnkPrefix:
    result = handlePrefix(arg, wrt)
  of nnkStmtListExpr:
    doAssert false, "Not required anymore, we untype the tree"
    doAssert arg[0].kind == nnkEmpty
    result = processExpr(arg[1], wrt)
  of nnkConv:
    doAssert false, "Not required anymore, we untype the tree"
    result = processExpr(arg[1], wrt)
  else: error("unsupported: " & $arg.kind & " and value " & $arg.n.treerepr)

proc sanitizeInput(n: NimNode): NimNode =
  # remove all `nnkConv, nnkHiddenStdConv and nnkStmtListExpr`
  let tree = n
  proc sanitize(n: NimNode): NimNode =
    if n.len == 0:
      case n.kind
      of nnkSym: result = ident(n.strVal)
      else: result = n
    else:
      case n.kind
      of nnkConv, nnkHiddenStdConv: result = n[1].sanitize
      of nnkStmtListExpr: result = n[1].sanitize
      else:
        result = newTree(n.kind)
        for ch in n:
          result.add sanitize(ch)
  result = tree.sanitize()

macro derivative*(arg, wrt: typed): untyped =
  ## computes the forward derivative of `arg` (a Nim expression)
  ## with respect to `wrt` using symbolic differentiation on the
  ## Nim AST
  let input = arg.sanitizeInput
  result = toNimCode processExpr(toSymbolicVariable(input), toSymbolicVariable(wrt.sanitizeInput))

template ∂*(arg, wrt: untyped): untyped =
  derivative(arg, wrt)

macro genHelpers(): untyped =
  ## Generate higher order derivative helpers.
  ##
  ## NOTE:
  ## It is really unwise to use the higher orders on functions that
  ## get larger after each derivative... :)
  let idx = ["²", "³", "⁴", "⁵", "⁶", "⁷", "⁸", "⁹"]
  result = newStmtList()
  let arg = ident"arg"
  let wrt = ident"wrt"
  for i, el in idx:
    let name = ident("∂" & $el)
    var body = newStmtList()
    for j in 0 ..< i + 2:
      if j == 0:
        body = quote do:
          ∂(`arg`, `wrt`)
      else:
        body = quote do:
          ∂(`body`, `wrt`)
    result.add quote do:
      template `name`*(`arg`, `wrt`: untyped): untyped =
        `body`

genHelpers()

when isMainModule:
  let x = 2.5
  echo ∂(x, x)

  template printAndCheck(arg, eq: untyped): untyped =
    echo "is ", derivative(arg, x), " should be ", eq
    echo derivative(arg, x), " is ", abs(derivative(arg, x) - eq) < 1e-4

  printAndCheck(exp(x), exp(x))
  printAndCheck(sin(x), cos(x))
  printAndCheck(cos(x), -sin(x))
  printAndCheck(tanh(x), sech(x)*sech(x))


  import ggplotnim, sequtils
  #
  #proc grad(x, y: float): float =
  #  #result = derivative(x*y + y*y*y, y)
  #  result = ∂(-2 * (sech(x) ^ 2) * (sech(x) ^ 2) + -2 * tanh(x) * (2 * (-tanh(x) * sech(x)) * pow(sech(x), 2 - 1.0'f64)), x)

  let xs = linspace(-5.0,5.0,1000)

  #echo ∂(∂(tanh(x), x), x)
  #let ys = xs.mapIt(grad(it, it))
  #ggplot(seqsToDf(xs, ys), aes("xs", "ys")) +
  #  geom_line() + ggsave("/tmp/deriv.pdf")


  #echo ∂(tanh(x), x)
  #echo ∂(sech(x)*sech(x), x)
  #echo ∂(-2 * sech(x) ^ 2 * sech(x) ^ 2 - 2 * tanh(x) * (2 * (-tanh(x) * sech(x)) * pow(sech(x), 2 - 1.0'f64)), x)


  #echo ∂(-2*tanh(x) * sech(x)^2, x)
  #echo ∂(sin(x) * cos(x) + pow(tanh(x), 2.0 - 1.0'f64), x)


  #echo ∂(4*tanh(x)^2 * sech(x)^2 - 2*sech(x)^4, x)
  #echo ∂(tanh(x), x)
  #echo ∂(∂(tanh(x), x), x)
  #echo ∂(∂(∂(tanh(x), x), x), x)
  #echo ∂(∂(∂(∂(tanh(x), x), x), x), x)
  var df = newDataFrame()
  block MultiGrad:

    block NoGrad:
      let ys = xs.mapIt(tanh(it))
      let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 0})
      echo dfLoc
      df.add dfLoc
    block Grad1:
      let ys = xs.mapIt(∂(tanh(it), it))
      let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 1})
      df.add dfLoc
    block Grad2:
      let ys = xs.mapIt(∂(∂(tanh(it), it), it))
      let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 2})
      df.add dfLoc
    block Grad3:
      let ys = xs.mapIt(∂(∂(∂(tanh(it), it), it), it))
      let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 3})
      df.add dfLoc
    block Grad4:
      let ys = xs.mapIt(∂(∂(∂(∂(tanh(it), it), it), it), it))
      let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 4})
      df.add dfLoc
    block Grad5:
      let ys = xs.mapIt(∂(∂(∂(∂(∂(tanh(it), it), it), it), it), it))
      let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 5})
      df.add dfLoc
    block Grad6:
      let ys = xs.mapIt(∂(∂(∂(∂(∂(∂(tanh(it), it), it), it), it), it), it))
      let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 6})
      df.add dfLoc
    #block Grad7:
    #  let ys = xs.mapIt(∂⁷(tanh(it), it))
    #  let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 7})
    #  df.add dfLoc
    #block Grad8:
    #  let ys = xs.mapIt(∂⁸(tanh(it), it))
    #  let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 8})
    #  df.add dfLoc

    ggplot(df, aes("x", "y", color = "grad")) +
      geom_line() +
      ggsave("/tmp/tanh_derivs.pdf")
