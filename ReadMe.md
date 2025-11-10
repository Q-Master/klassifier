**klassifier** - is a nim sugar macro library for class emulation and VT emulation.
====

Macro library to create some OOP sugar for nim to not use original slow nim methods.

```nim
class TestClass:
  var local: int
  var public*: float
  
  proc justAProc(x: int, y: float): int = (x+y).int
  method testmethod*(self: TestClass) = echo testmethod(self.local, self.public)

class Test1Class of TestClass:
  method testmethod*(self: Test1Class) = 
    echo "overloaded"
    super Test1Class, testmethod(self)
```

Overview
--------

This library includes two macros:
  - *class* macro to make an emulated class.
  - *super* macro to call parent overloaded functions.


### The *class* macro

This macro is used to create the class type with all needed initializations. The macro supports:
 - let and var (not differ in implementation) variable declaration
 - method for virtual methods declaration (converted internally to proc with some additional initializations)
 - proc for just a simple proc.

Methods are checked to contain the first param of the type of current class otherwise they're added as a simple proc.
Methods which pass all the checks are marked as a virtual and added to vtable (very simple implementation).  
The `=destroy` method marks destructor and correctly supported by class code generator.  
The `=new` method marks constructor. The resulting code will be modified to correctly initialize VT of the class.

### The *super* macro

This macro is used to call parent overloaded functions. The function is checked to be overloaded and if yes the call 
is subsituted to call parent function.
