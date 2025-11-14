import std/[macros, tables, strutils, sequtils]

export macros


type
  TCacheItem = object
    basename: string = ""
    allVMethods: seq[string] = @[]


var classCache {.compiletime, global.}: Table[string, TCacheItem]


proc getNameAndBase(head: NimNode): (NimNode, string) {.compiletime.} =
  ## Parses the head of the class macro and returns class name and
  ## it's base if set. If not - string will be empty.
  ## Will preserve the line info of the class name.

  var classname: NimNode
  var basename: string
  case head.kind
  of nnkIdent:
    classname = head.copy
  of nnkInfix:
    if eqIdent(head[0], "of"):
      classname = head[1].copy
      case head[2].kind
      of nnkIdent:
        basename = $head[2]
      else:
        error("Error in class parents", head[2])
    else:
      classname = head[1].copy
  else:
    error("Error in class header " & head.treeRepr, head)
  result = (classname, basename)


proc getProcName(callable: NimNode): (string, LineInfo) {.compiletime.} =
  ## Returns the proc/method name and coresponding lineinfo.

  if callable.kind in [nnkProcDef, nnkMethodDef]:
    let en = callable[0]
    case en.kind
    of nnkIdent:
      result = ($en, en.lineInfoObj)
    of nnkPostfix:
      if en[1].kind == nnkIdent:
        result = ($en[1], en[1].lineInfoObj)
      else:
        result = ($en[1][0] & $en[1][1], en[1].lineInfoObj)
    of nnkAccQuoted:
      result = ($en[0] & $en[1], en.lineInfoObj)
    else:
      raise newException(ValueError, "Element is unknown")
  else:
    raise newException(ValueError, "Element is not a function")


proc getAllParamNames(params: NimNode): seq[NimNode] {.compiletime.} =
  ## Returns all the params of nnkFormalParams of the proc/method
  ## Will preserve the line info.

  if params.kind == nnkFormalParams:
    for pd in params.children:
      if pd.kind == nnkIdentDefs:
        for i in 0 ..< pd.len-2:
          result.add(pd[i].copy)


proc getMethodClass(methodName: string, base: string): string {.compiletime.} =
  ## Finds the base class implementation for the method name.
  ## Returns empty string if not found.

  var curBase = base
  while true:
    if classCache.hasKey(curBase):
      if methodName.toLower in classCache[curBase].allVMethods:
        result = curBase
        break
      else:
        curBase = classCache[curBase].basename
    else:
      break


proc rename(someIdent: NimNode, newName: string): NimNode {.compiletime.} =
  ## Renames ident to a new name.
  ## Will preserve the line info.

  let nname = ident newName
  nname.copyLineInfo(someIdent)
  result =
    case someIdent.kind
    of nnkIdent:
      nname
    of nnkPostfix:
      nnkPostfix.newTree(
        ident "*",
        nname
      )
    else:
      raise newException(ValueError, "Unknown method/proc")


proc convMethodToProc(callable: NimNode, newName: string = ""): NimNode {.compiletime.} =
  ## Converts the method to proc with possible rename.
  ## Will preserve the line info.

  result = newProc(
    (
      if newName.len > 0:
        callable[0].rename(newName)
      else:
        callable[0].copy
    ),
    callable[3].children.toSeq,
    body = callable[6].copy,
    pragmas = callable[4].copy
  )
  result.copyLineInfo(callable)


proc createClassParamNode(letVar: NimNode): NimNode {.compiletime.} =
  ## Creates class parameter node from var/let node.
  ## Will preserve the line info

  let trueElem = letVar[0]
  case trueElem[0].kind
  of nnkPostfix, nnkIdent:
    # simple exportable fields
    result = nnkIdentDefs.newTree(
      trueElem[0].copy,
      trueElem[1].copy,
      trueElem[2].copy
    )
  of nnkPragmaExpr:
    # added some pragmas
    result = nnkIdentDefs.newTree(
      trueElem[0][0].copy,
      trueElem[1].copy,
      trueElem[2].copy
    )
  else:
    error("Unknown var section " & $trueElem[0].kind, trueElem[0])
  result.copyLineInfo(letVar)


proc createMethodVTVar(name: NimNode, params: NimNode): NimNode {.compiletime.} =
  result = nnkIdentDefs.newTree(
    nnkPostfix.newTree(
      ident "*",
      name
    ),
    nnkProcTy.newTree(
      params,
      nnkPragma.newTree(
        ident "nimcall"
      )
    ),
    newEmptyNode()
  )


proc createProcNodes(virtualMethod: NimNode, classname: string, basename: string, varlist: var NimNode): (seq[NimNode], seq[NimNode]) {.compiletime.} =
  ## Create proc nodes for method, it's implementation if there's no any
  ## Create init statement for VT variable for method impl.
  ## If method has no first param of type `classname` then it's just copied to resulting list untouched

  var methods: seq[NimNode]
  var initList: seq[NimNode]
  let (methodName, infoObj) = virtualMethod.getProcName()
  let methodNameV = ident (methodName & "V")
  methodNameV.setLineInfo(infoObj)
  let methodNameImpl = classname.toLower & methodName & "Impl"
  let methodNameImplC = classname.toLower & methodName & "ImplC"

  if (virtualMethod[3].len > 1) and ($(virtualMethod[3][1][1]) == classname):
    # first param is self
    #   - check all the base classes to have any of the same method names
    let mc = getMethodClass(methodName, basename)
    #     - if not
    initList.add(
      nnkAsgn.newTree(
        nnkDotExpr.newTree(
          ident "self",
          methodNameV
        ),
        ident methodNameImpl
      )
    )
    var realCall: NimNode
    var realProc: NimNode
    var copiedElem: NimNode

    if mc.len == 0:
      classCache[classname].allVMethods.add(methodName.toLower)
      #       - add proc with original name which calls the virtual method
      realCall = newCall(nnkDotExpr.newTree(ident "self", methodNameV), getAllParamNames(virtualMethod[3]))
      realProc = newProc(
        virtualMethod[0].copy,
        virtualMethod[3].children.toSeq,
        body = newStmtList(
          if virtualMethod[3][0].kind == nnkEmpty:
            realCall
          else:
            newAssignment(
              ident "result",
              realCall
            )
        ),
        pragmas = virtualMethod[4].copy
      )
      methods.add(realProc)
      #       - rename the original method to **Impl and add it. set the lineInfoObj to it
      copiedElem = convMethodToProc(virtualMethod, methodNameImpl)
      copiedElem.setLineInfo(virtualMethod.lineInfoObj)
      methods.add(copiedElem)
      #       - add type public variable with **V name and type proc (self: ClassType, ....) {.nimcall.}
      varlist.add(createMethodVTVar(methodNameV, copiedElem[3].copy))
    else:
      #     - otherway
      #       - rename the original method to **ImplC and add it. set the lineInfoObj to it
      copiedElem = convMethodToProc(virtualMethod, methodNameImplC)
      copiedElem.setLineInfo(virtualMethod.lineInfoObj)
      methods.add(copiedElem)
      #       - create proc with type conversions from found base to current type, name it as **Impl
      var realCallParams = getAllParamNames(virtualMethod[3])
      realCallParams[0] = nnkCast.newTree(ident classname, ident "s")
      realCall = newCall(methodNameImplC, realCallParams)
      var realProcParams = virtualMethod[3].children.toSeq
      realProcParams[1] = nnkIdentDefs.newTree(ident "s", ident mc, newEmptyNode())
      realProc = newProc(
        virtualMethod.rename(methodNameImpl),
        realProcParams,
        body = newStmtList(
          if virtualMethod[3][0].kind == nnkEmpty:
            realCall
          else:
            newAssignment(
              ident "result",
              realCall
            )
        ),
        pragmas = virtualMethod[4].copy
      )
      methods.add(realProc)
  else:
    # no params, or first param has other type
    methods.add(convMethodToProc(virtualMethod))
  result = (methods, initList)


proc createInitVTMethod(classname: NimNode, initlines: seq[NimNode], basename: string = ""): NimNode {.compiletime.} =
  ## Create method which initializes VT for that particular class
  ## If class has parent call to parent initVT will be issued.

  var stmts = newStmtList()
  if basename.len > 0:
    stmts.add(
      newCall("initVT",
        nnkCast.newTree(
          ident basename,
          ident "self"
        )
      )
    )
  stmts.add(initlines)

  result = nnkProcDef.newTree(
    nnkPostfix.newTree(
      ident "*",
      ident "initVT"
    ),
    newEmptyNode(),
    newEmptyNode(),
    nnkFormalParams.newTree(
      newEmptyNode(),
      nnkIdentDefs.newTree(
        ident "self",
        classname,
        newEmptyNode()
      )
    ),
    newEmptyNode(),
    newEmptyNode(),
    stmts
  )


proc createDestroyMethod(classname: string, destroyMethod: NimNode): NimNode {.compiletime.}=
  ## Create `=destroy` proc from method
  ## For classes with destructor it is created 2 type nodes, so the 1st param type is renamed to `classname`+Obj
  result = convMethodToProc(destroyMethod)
  let lineinfo = result[3][1][1].lineInfoObj
  result[3][1][1] = ident classname & "Obj"
  result[3][1][1].setLineInfo(lineinfo)
  result.setLineInfo(destroyMethod.lineInfoObj)


proc createCreateMethod(classname: NimNode, createMethod: NimNode = nil): seq[NimNode] {.compiletime.} =
  ## Create implicitly constructor proc with name new+`classname`
  ## Additionally if `createMetod` is not empty - create `init` proc with contents of `createMethod`

  var newIdent = ident "new" & $classname
  let newProc = nnkProcDef.newTree(
    nnkPostfix.newTree(
      ident "*",
      newIdent
    ),
    newEmptyNode(),
    newEmptyNode(),
    nnkFormalParams.newTree(
      classname,
    ),
    newEmptyNode(),
    newEmptyNode(),
    nnkStmtList.newTree(
      newCall("new", ident "result"),
      newCall("initVT", ident "result")
    )
  )
  if not createMethod.isNil:
    let (_, lineinfo) = createMethod.getProcName()
    var initNode = ident "init"
    initNode.setLineInfo(lineinfo)
    newIdent.setLineInfo(lineinfo)
    var methFormalParams = createMethod[3].copy()
    methFormalParams.del(0, 1)
    var initProc = nnkProcDef.newTree(
      nnkPostfix.newTree(
        ident "*",
        initNode
      ),
      newEmptyNode(),
      newEmptyNode(),
      nnkFormalParams.newTree(
        newEmptyNode(),
        nnkIdentDefs.newTree(
          ident "self",
          classname,
          newEmptyNode()
        )
      ),
      newEmptyNode(),
      newEmptyNode(),
      nnkStmtList.newTree()
    )
    createMethod[6].copyChildrenTo(initProc[6])

    for fp in methFormalParams.children:
      newProc[3].add(fp.copy)
      initProc[3].add(fp.copy)
    var params = getAllParamNames(methFormalParams)
    params.insert(ident "result", 0)
    let initCall = newCall("init", params)
    newProc[6].add(initCall)
    initProc.copyLineInfo(createMethod)
    result.add(initProc)
  result.add(newProc)


proc createType(classname: NimNode, basename: string, body: NimNode): (seq[NimNode], seq[NimNode]) =
  var reclist = newNimNode(nnkRecList)
  var methods: seq[NimNode] = @[]
  var initLines: seq[NimNode] = @[]
  var hasDestructor = false
  var constructor: seq[NimNode]
  for elem in body.children:
    case elem.kind
    of nnkVarSection, nnkLetSection:
      # Variable definition
      reclist.add(elem.createClassParamNode)
    of nnkMethodDef:
      ## Virtual method
      ## - check if first param is of self type or any base type
      ## - if yes
      ##   - check all the base classes to have any of the same method names
      ##     - if not
      ##       - add type public variable with **V name and type proc (self: ClassType, ....) {.nimcall.}
      ##       - rename the original method to **Impl and add it. set the lineInfoObj to it
      ##       - add proc with original name which calls the virtual method
      ##     - otherway
      ##       - rename the original method to **ImplC and add it. set the lineInfoObj to it
      ##       - create proc with type conversions, name it as **Impl
      ##   - add line to init method which sets **V variable to **Impl method
      ## - otherway
      ##   - just make a proc from the method and put it to statement list
      let (procname, _) = elem.getProcName()
      if procname == "=destroy":
        # Create destructor method
        hasDestructor = true
        methods.insert(createDestroyMethod($classname, elem), 0)
      elif procname == "=new":
        # Create constructor method
        constructor = createCreateMethod(classname, elem)
      else:
        let (pn, il) = elem.createProcNodes($classname, basename, reclist)
        if pn.len > 0:
          methods.add(pn)
        if il.len > 0:
          initLines.add(il)
    of nnkProcDef:
      ## Non-virtual method
      ## - just add the proc to the statement list and set lineInfoObj to it
      let (procname, _) = elem.getProcName()
      if procname == "=destroy":
        error "Destructor must be marked as method"
      elif procname == "=new":
        error "Constructor must be marked as method"
      else:
        let ec = elem.copy()
        ec.setLineInfo(elem.lineInfoObj)
        methods.add(ec)
    else:
      discard

  var theType: seq[NimNode] = @[]
  if hasDestructor:
    # For classes with destructor, create class object and a class ref object
    let cobj = ($classname & "Obj").ident
    theType.add(
      nnkTypeDef.newTree(
        nnkPostfix.newTree(
          ident "*",
          classname
        ),
        newEmptyNode(),
        nnkRefTy.newTree(
          cobj
        )
      )
    )
    theType.add(
      nnkTypeDef.newTree(
        nnkPostfix.newTree(
          ident "*",
          cobj
        ),
        newEmptyNode(),
        nnkObjectTy.newTree(
          newEmptyNode(),
          (
            nnkOfInherit.newTree(
              (if basename.len > 0: basename.ident else: ident "RootObj")
            )
          ),
          reclist
        )
      )
    )
  else:
    # For destructorless classes just create ref object
    theType.add(
      nnkTypeDef.newTree(
        nnkPostfix.newTree(
          ident "*",
          classname
        ),
        newEmptyNode(),
        nnkRefTy.newTree(
          nnkObjectTy.newTree(
            newEmptyNode(),
            (
              nnkOfInherit.newTree(
                (if basename.len > 0: basename.ident else: ident "RootObj")
              )
            ),
            reclist
          )
        )
      )
    )
  if initLines.len == 0:
    initLines.add(
      nnkDiscardStmt.newTree(newEmptyNode())
    )
  methods.add(createInitVTMethod(classname, initLines))
  if constructor.len > 0:
    methods.add(constructor)
  else:
    methods.add(createCreateMethod(classname, nil))
  result = (theType, methods)


macro class*(head, body: untyped): untyped =
  let (classname, basename) = getNameAndBase(head)
  result = newStmtList()
  if classCache.hasKey($classname):
    when defined(nimsuggest):
      classCache.del($classname)
    else:
      error("Duplicate class " & $classname, head)
  classCache[$classname] = TCacheItem(basename: basename)
  var (typeNodes, methods) = createType(classname, basename, body)
  var ts = newNimNode(nnkTypeSection, body).add(typeNodes)
  result.add(ts)
  result.add(newStmtList(methods))
  echo result.repr


#[
macro super*(classname, body: untyped): untyped =
  if classname.kind notIn [nnkIdent, nnkSym]:
    error "Class name should be a valid name"
  let cn = $classname
  if body.kind != nnkCall:
    error "Only callable could be used in a super"
  if classCache.hasKey(cn) and classCache[cn].basename != "":
    let fn: string = (
      if body[0].kind == nnkIdent:
        $body[0]
      elif body[0].kind == nnkDotExpr:
        $body[0][1]
      else:
        error "Unknown call"
    )
    let mc = findMethodClass(fn, classCache[cn].basename)
    if mc.len > 0:
      var allparams: seq[NimNode]
      for param in body:
        allparams.add(param)
      if body[0].kind == nnkIdent:
        allparams[0] = ident mc.toLower() & fn & "Impl"
        allparams[1] = nnkCast.newTree(
          ident mc,
          allparams[1].copy
        )
      else:
        allparams[0][0] = nnkCast.newTree(
          ident mc,
          allparams[0][0].copy
        )
        allparams[0][1] = ident mc.toLower() & fn & "Impl"
      result = nnkCall.newTree()
      for param in allparams:
        result.add(param)
    else:
      result = body.copy()
  else:
    error "Unknown super class for " & cn
]#
