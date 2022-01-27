import macros, tables, math

type
  SymbolKind = enum
    skPlus, skMinus, skMul, skDiv, skPower, skInvalid
  SymbolicVariable = object
    n: NimNode # the corresponding nim node
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
    #echo fn[2].treerepr
    FunctionTab[fnName] = fnId
    DerivativeTab[fnName] = SymbolicFunction(n: fn[2], processed: true)
  #for k, v in FunctionTab:
  #  echo "Fn ", k.repr
  #  echo "Deriv ", DerivativeTab[k].repr

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
  result = SymbolicVariable(n: repl, processed: true)

proc isNumber(n: NimNode): bool =
  # maybe this: ?
  n.typeKind in {ntyInt .. ntyUInt64}

proc isZero(x: SymbolicVariable): bool = x.n.kind in {nnkFloatLit, nnkFloat64Lit} and x.n.floatVal == 0.0
proc isOne(x: SymbolicVariable): bool = x.n.kind in {nnkFloatLit, nnkFloat64Lit} and x.n.floatVal == 1.0

proc name(fn: SymbolicFunction): string = result = fn.n.strVal

proc toSymbolicVariable(n: NimNode, processed = false): SymbolicVariable =
  #doAssert n.kind in {nnkIdent, nnkSym, nnkIntLit .. nnkFloat128Lit}
  result = SymbolicVariable(n: n, processed: processed)

proc symbolicOne(): SymbolicVariable =
  SymbolicVariable(n: newLit(1.0), processed: true)

proc symbolicZero(): SymbolicVariable =
  SymbolicVariable(n: newLit(0.0), processed: true)

proc symbolicPower(): SymbolicParameter =
  SymbolicParameter(n: ident"^", kind: skPower)

proc `==`(a, b: SymbolicVariable): bool =
  result = a.n == b.n

## TODO: simplify these such that if the second arg is identity element, not included
proc `-`(n: SymbolicVariable): SymbolicVariable =
  result = SymbolicVariable(n: nnkCall.newTree(ident"-", n.n), processed: true)

proc setProcessed(x: SymbolicVariable): SymbolicVariable =
  result = x
  result.processed = true # most likely already true

proc `+`(x, y: SymbolicVariable): SymbolicVariable =
  if x.isZero: result = y.setProcessed
  elif y.isZero: result = x.setProcessed
  else: result = SymbolicVariable(n: nnkInfix.newTree(ident"+", x.n, y.n), processed: true)

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
  elif x.n.isNumber and y.n.isNumber: # compute result in place
    result = SymbolicVariable(n: litDiff(x.n, y.n), processed: true)
  else: result = SymbolicVariable(n: nnkInfix.newTree(ident"-", x.n, y.n), processed: true)

proc `-`(x: SymbolicVariable, y: SomeNumber): SymbolicVariable =
  result = x - toSymbolicVariable(newLit(y), true)

proc `*`(x, y: SymbolicVariable): SymbolicVariable =
  if x.isOne: result = y.setProcessed
  elif y.isOne: result = x.setProcessed
  elif x.isZero: result = symbolicZero()
  elif y.isZero: result = symbolicZero()
  else: result = SymbolicVariable(n: nnkInfix.newTree(ident"*", x.n, y.n), processed: true)

proc `/`(x, y: SymbolicVariable): SymbolicVariable =
  # if x is one, default is shortest already
  if y.isZero: error("Computation contains division by 0!")
  elif x.isZero: result = symbolicZero()
  elif y.isOne: result = x.setProcessed
  elif x == y: result = symbolicOne()
  else: result = SymbolicVariable(n: nnkInfix.newTree(ident"/", x.n, y.n), processed: true)

proc `^`(x, y: SymbolicVariable): SymbolicVariable =
  # if x is one, default is shortest already
  ## XXX: add int literals for powers so that we don't have to force `pow` here!
  if y.isOne: result = x.setProcessed
  elif y.isZero: result = symbolicOne()
  elif x.isZero: result = symbolicZero()
  else: result = SymbolicVariable(n: nnkCall.newTree(ident"pow", x.n, y.n), processed: true)

proc log(x: SymbolicVariable): SymbolicVariable =
  if x.isZero: error("Computation yields log(0) and thus -Inf!")
  else: result = SymbolicVariable(n: nnkCall.newTree(ident"log", x.n), processed: true)

proc differentiate(x, wrt: SymbolicVariable): SymbolicVariable =
  if x.processed:
    result = x
  else:
    if x == wrt: result = symbolicOne()
    else: result = symbolicZero()
  echo "differentiate: ", result.n.repr, " of args ", x.n.repr, " and ", wrt.n.repr

proc diffPlus(x, y, wrt: SymbolicVariable): SymbolicVariable =
  # compute gradient of `x + y` w.r.t. `wrt`
  echo "diffPlus of ", x.repr, " and ", y.repr, " wrt ", wrt.repr
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
  # compute gradient of `x + y` w.r.t. `wrt`
  echo "In diff power : "
  echo "x ", x.n.repr
  echo "y ", y.n.repr
  echo "wrt ", wrt.n.repr
  let xp = differentiate(x, wrt)
  let yp = differentiate(y, wrt)
  echo "xp ", xp.n.repr, " is zero ? ", xp.isZero
  echo "yp ", yp.n.repr, " is zero ? ", yp.isZero
  if xp.isZero and yp.isZero:
    result = symbolicZero()
  elif yp.isZero:
    echo "y is zero!"
    result = y * xp  * (x ^ (y - 1.0))
    echo "result ?? ", result.n.repr
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

proc parseSymbolicParameter(n: NimNode): SymbolicParameter =
  doAssert n.kind in {nnkIdent, nnkSym}
  case n.strVal
  of "+": result = SymbolicParameter(n: n, kind: skPlus)
  of "-": result = SymbolicParameter(n: n, kind: skMinus)
  of "*": result = SymbolicParameter(n: n, kind: skMul)
  of "/": result = SymbolicParameter(n: n, kind: skDiv)
  of "^", "**": result = SymbolicParameter(n: n, kind: skPower)
  else: result = SymbolicParameter(n: newEmptyNode(), kind: skInvalid)

proc parseSymbolicFunction(n: NimNode): SymbolicFunction =
  doAssert n.kind in {nnkIdent, nnkSym}
  result = SymbolicFunction(n: FunctionTab[n.strVal])

proc toNimCode(x: SymbolicVariable): NimNode = x.n

proc processExpr(arg, wrt: NimNode): SymbolicVariable
proc handleInfix(arg, wrt: NimNode): SymbolicVariable =
  echo "In INFIX with: ", arg.repr
  doAssert arg.kind == nnkInfix
  let symbol = parseSymbolicParameter(arg[0])
  let ch1 = toSymbolicVariable(arg[1])#processExpr(arg[1], wrt)
  let ch2 = toSymbolicVariable(arg[1])#processExpr(arg[2], wrt)
  echo "Ch1 ", ch1.repr, " and ch2 ", ch2.repr
  result = differentiate(symbol, ch1, ch2, toSymbolicVariable wrt)
  echo "infix result ", result.n.repr

proc handleCall(arg, wrt: NimNode): SymbolicVariable =
  ## handle chain rule
  doAssert arg.kind == nnkCall, " is : " & $arg.treerepr
  # check if call might be an `infix` symbol. If so, patch up and call infix instead
  if arg[0].parseSymbolicParameter().kind != skInvalid:
    var inf = nnkInfix.newTree()
    for ch in arg:
      inf.add ch
    result = handleInfix(inf, wrt)
  else:
    # regular function call
    #doAssert arg.len == 2, "Only single argument functions supported for now! Was: " & $arg.treerepr
    # for now assume single argument functions, i.e. we can evaluate the argument
    # as an expression and there is only one argument
    if arg[0].strVal == "pow":
      # power is special case, as it's the only 2 arg function we support so far
      let ch1 = processExpr(arg[1], wrt)
      let ch2 = processExpr(arg[2], wrt)
      result = differentiate(symbolicPower(), ch1, ch2, toSymbolicVariable wrt)
    else:
      let fn = parseSymbolicFunction(arg[0])
      let arg = processExpr(arg[1], wrt) # `processExpr` performs the derivative for us
      result = differentiate(arg, toSymbolicVariable wrt) * differentiate(fn, arg) # chain rule: outer * inner

proc handlePrefix(arg, wrt: NimNode): SymbolicVariable =
  ## handle prefix, usually `-` or `+`
  expectKind(arg, nnkPrefix)
  # parse the prefix symbol
  let fn = parseSymbolicParameter(arg[0])
  case fn.kind
  of skPlus, skMinus:
    let ch1 = processExpr(arg[1], wrt)
    result = differentiate(fn, ch1,
                           symbolicZero(), # `-` or `+` zero is identity,
                           toSymbolicVariable wrt)
  else:
    error("Invalid prefix: " & $fn.n.repr & " from argument: " & $arg.repr)

proc processExpr(arg, wrt: NimNode): SymbolicVariable =
  case arg.kind
  of nnkSym, nnkIntLit .. nnkFloat128Lit:
    if arg.isNumber: result = toSymbolicVariable(arg)
    else:
      # need to check if it's a call, not supported yet
      error("Not supported! " & $arg.typeKind & " of node: " & $arg.repr)
  of nnkInfix:
    result = handleInfix(arg, wrt)
  of nnkCall:
    result = handleCall(arg, wrt)
  of nnkHiddenStdConv:
    # assume contains literals?
    if arg.isNumber or arg.typeKind == ntyRange:
      result = processExpr(arg[1], wrt)
    else:
      error("unsupported: " & $arg.kind & " and value " & $arg.treerepr)
  of nnkPrefix:
    result = handlePrefix(arg, wrt)
  else: error("unsupported: " & $arg.kind & " and value " & $arg.treerepr)
  echo "Arg: ", arg.repr, " of kind ", arg.kind, " produced ", result.n.repr, " for ", wrt.repr

macro derivative(arg, wrt: typed): untyped =
  ## computes the forward derivative of `arg` (a Nim expression)
  ## with respect to `wrt`
  #echo "ARGUMENT ", arg.treerepr
  #doAssert arg.kind == nnkInfix
  # for now only support pure infix
  # TODO: handle calls, command
  result = toNimCode processExpr(arg, wrt)
  echo result.treerepr
  echo "∂ result\n\n", result.repr

template ∂(arg, wrt: untyped): untyped =
  derivative(arg, wrt)


let x = 2.5
#let y = 5.0
#
#echo derivative(exp(x), x)
#template printAndCheck(arg, eq: untyped): untyped =
#  echo "is ", derivative(arg, x), " should be ", eq
#  echo derivative(arg, x), " is ", abs(derivative(arg, x) - eq) < 1e-4
#
#printAndCheck(exp(x), exp(x))
#printAndCheck(sin(x), cos(x))
#printAndCheck(cos(x), -sin(x))
#printAndCheck(tanh(x), sech(x)*sech(x))
#
#import ggplotnim, sequtils
#
#proc grad(x, y: float): float =
#  result = derivative(x*y + y*y*y, y)
#
#let xs = linspace(-5.0,5.0,1000)
#let ys = xs.mapIt(grad(x, it))
#ggplot(seqsToDf(xs, ys), aes("xs", "ys")) +
#  geom_line() + ggsave("/tmp/deriv.pdf")


#(sech(it) ^ 2 * (-tanh(it) * sech(it)) + sech(it) ^ 2 * (-tanh(it) * sech(it))) *
#  pow(sech(it) ^ 2 * (-tanh(it) * sech(it)) +
#      sech(it) ^ 2 * (-tanh(it) * sech(it)), 0.0)


echo ∂(sech(x)*sech(x), x)
#var df = newDataFrame()
#block MultiGrad:
#
#  block NoGrad:
#    let ys = xs.mapIt(tanh(it))
#    let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 0})
#    echo dfLoc
#    df.add dfLoc
#  block Grad1:
#    let ys = xs.mapIt(∂(tanh(it), it))
#    let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 1})
#    df.add dfLoc
#  block Grad2:
#    let ys = ∂(∂(tanh(x), x), x)
#    let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 2})
#    df.add dfLoc
#  #block Grad3:
#  #  let ys = xs.mapIt(∂(∂(∂(tanh(it), it), it), it))
#  #  let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 3})
#  #  df.add dfLoc
#  #block Grad4:
#  #  let ys = xs.mapIt(∂(∂(∂(∂(tanh(it), it), it), it), it))
#  #  let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 4})
#  #  df.add dfLoc
#  #block Grad5:
#  #  let ys = xs.mapIt(∂(∂(∂(∂(∂(tanh(it), it), it), it), it), it))
#  #  let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 5})
#  #  df.add dfLoc
#  #block Grad5:
#  #  let ys = xs.mapIt(∂(∂(∂(∂(∂(∂(tanh(it), it), it), it), it), it), it))
#  #  let dfLoc = seqsToDf({"x" : xs, "y" : ys, "grad" : 6})
#  #  df.add dfLoc
#
#  ggplot(df, aes("x", "y", color = "grad")) +
#    geom_line() +
#    ggsave("/tmp/tanh_derivs.pdf")
