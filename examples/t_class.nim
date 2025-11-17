import ../klassifier


class TClass:
  var x: int
  var x1*: int
  var x2: int = 8
  var x3*: int = 8
  let y: float
  let y1*: float
  let y2: float = 1.0
  let y3*: float = 1.0
  method tMethod(self: TClass) = echo "TCLASS tmethod"
  method tMethod1*(self: TClass) = echo "TCLASS tmethod1"
  method tMethod2(self: TClass) = discard
  proc tProc(self: TClass) = discard
  proc tProc1*(self: TClass) = discard
  method `=new`*(x: int) = echo $x


class TClass1 of TClass:
  method tMethod(self: TClass1) = echo "TCLASS1 tmethod"
  method tMethod3(self: TClass1) = discard
  method `=destroy`*(self: TClass1) = echo "DESTRUCTION"
  method `=new`*() =
    echo "CONSTRUCTION"
    #echo x
    cast[TClass](self).init(8)


proc x(self: TClass1) =
  self.super tMethod()

let cls = newTClass1()

cls.tMethod()
TClass1.super tMethod(cls)
TClass1.super cls.tMethod()
cast[TClass](cls).init(8)
cls.x()
