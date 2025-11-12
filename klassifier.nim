import std/[macros, tables, strutils, sequtils]

export macros


type
  TCacheItem = object
    basename: string = ""
    allVMethods: seq[string] = @[]


var classCache {.compiletime, global.}: Table[string, TCacheItem]


proc getNameAndBase(head: NimNode): (string, string) {.compiletime.} =
  var classname: NimNode
  var basename: string
  case head.kind
  of nnkIdent:
    classname = head
  of nnkInfix:
    if eqIdent(head[0], "of"):
      classname = head[1]
      case head[2].kind
      of nnkIdent:
        basename = $head[2]
      else:
        error("Error in class parents", head[2])
    else:
      classname = head[1]
  else:
    error("Error in class header", head)
  result = ($classname, basename)


proc getProcName(element: NimNode): string {.compiletime.} =
  if element.kind in [nnkProcDef, nnkMethodDef]:
    let en = element[0]
    case en.kind
    of nnkIdent:
      result = $en
    of nnkPostfix:
      if en[1].kind == nnkIdent:
        result = $en[1]
      else:
        result = $en[1][0] & $en[1][1]
    of nnkAccQuoted:
      result = $en[0] & $en[1]
    else:
      raise newException(ValueError, "Element is unknown")
  else:
    raise newException(ValueError, "Element is not a function")


proc findMethodClass(methodName: string, base: string): string {.compiletime.} =
  var curBase = base
  while true:
    if classCache.hasKey(curBase):
      if methodName in classCache[curBase].allVMethods:
        result = curBase
        break
      else:
        curBase = classCache[curBase].basename
    else:
      break


proc genVarNode(field: NimNode): NimNode {.compiletime.} =
  case field.kind
  of nnkPostfix:
    # var field*: type
    result = nnkPostfix.newTree(
      ident "*",
      field[1].copy
    )
  of nnkIdent:
    # var field: type
    result = field.copy
  else:
    error("Unknown var section " & $field.kind, field)


proc addVarNode(reclist: var NimNode, elem: NimNode) {.compiletime.} =
  # field = trueElem[0]
  let trueElem = elem[0]
  var typeNode: NimNode
  case trueElem[0].kind
  of nnkPostfix, nnkIdent:
    # simple exportable fields
    let fieldNode = genVarNode(trueElem[0])
    typeNode = nnkIdentDefs.newTree(
      fieldNode,
      trueElem[1].copy,
      trueElem[2].copy
    )
  of nnkPragmaExpr:
    # added some pragmas
    let fieldNode = genVarNode(trueElem[0][0])
    typeNode = nnkIdentDefs.newTree(
      fieldNode,
      trueElem[1].copy,
      trueElem[2].copy
    )
  else:
    error("Unknown var section " & $trueElem[0].kind, trueElem[0])
  typeNode.setLineInfo(elem.lineInfoObj)
  reclist.add(typeNode)


proc renameProc(elem: NimNode, newName: string): NimNode {.compiletime.} =
  result =
    case elem[0].kind
    of nnkIdent:
      ident newName
    of nnkPostfix:
      nnkPostfix.newTree(
        ident "*",
        ident newName
      )
    else:
      raise newException(ValueError, "Unknown method")


proc convMethodToProc(elem: NimNode, newName: string = ""): NimNode {.compiletime.} =
  result = newProc(
    (
      if newName.len > 0:
        elem.renameProc(newName)
      else:
        elem[0].copy
    ),
    elem[3].children.toSeq,
    body = elem[6].copy,
    pragmas = elem[4].copy
  )


proc createProcVar(name: string, params: NimNode): NimNode {.compiletime.} =
  result = nnkIdentDefs.newTree(
    nnkPostfix.newTree(
      ident "*",
      ident name
    ),
    nnkProcTy.newTree(
      params,
      nnkPragma.newTree(
        ident "nimcall"
      )
    ),
    newEmptyNode()
  )


proc getAllParamNames(params: NimNode): seq[NimNode] {.compiletime.} =
  for pd in params.children:
    if pd.kind == nnkIdentDefs:
      for i in 0 ..< pd.len-2:
        result.add(pd[i])


proc addProcNode(methods: var seq[NimNode], classname: string, basename: string, virtualMethod: NimNode, varlist: var NimNode): seq[NimNode] {.compiletime.} =
  let methodName = (if virtualMethod[0].kind == nnkIdent: $virtualMethod[0] else: $virtualMethod[0][1])
  let methodNameV = methodName & "V"
  let methodNameImpl = classname.toLower & methodName & "Impl"
  let methodNameImplC = classname.toLower & methodName & "ImplC"

  if (virtualMethod[3].len != 0) and ($(virtualMethod[3][1][1]) == $classname):
    # first param is self
    #   - check all the base classes to have any of the same method names
    let mc = findMethodClass(methodName, basename)
    #     - if not
    result.add(
      nnkAsgn.newTree(
        nnkDotExpr.newTree(
          ident "self",
          ident methodNameV
        ),
        ident methodNameImpl
      )
    )
    var realCall: NimNode
    var realProc: NimNode
    var copiedElem: NimNode

    if mc.len == 0:
      classCache[classname].allVMethods.add(methodName)
      #       - add proc with original name which calls the virtual method
      realCall = newCall(nnkDotExpr.newTree(ident "self", ident methodNameV), getAllParamNames(virtualMethod[3]))
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
      varlist.add(createProcVar(methodNameV, copiedElem[3].copy))
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
        virtualMethod.renameProc(methodNameImpl),
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


proc createDestroyMethod(classname: string, destroyMethod: NimNode): NimNode {.compiletime.}=
  result = convMethodToProc(destroyMethod)
  result[3][1][1] = ident classname & "Obj"
  result.setLineInfo(destroyMethod.lineInfoObj)


proc createCreateMethod(classname: string, createMethod: NimNode = nil): NimNode {.compiletime.} =
  result = nnkStmtList.newTree()
  let newProc = nnkProcDef.newTree(
    nnkPostfix.newTree(
      ident "*",
      ident "new" & classname
    ),
    newEmptyNode(),
    newEmptyNode(),
    nnkFormalParams.newTree(
      ident classname,
    ),
    newEmptyNode(),
    newEmptyNode(),
    nnkStmtList.newTree(
      newCall("new", ident "result"),
      newCall("initVT", ident "result")
    )
  )
  if not createMethod.isNil:
    let methFormalParams = createMethod[3].copy()
    methFormalParams.del(0, 1)
    let initProc = nnkProcDef.newTree(
      nnkPostfix.newTree(
        ident "*",
        ident "init"
      ),
      newEmptyNode(),
      newEmptyNode(),
      nnkFormalParams.newTree(
        newEmptyNode(),
        nnkIdentDefs.newTree(
          ident "self",
          ident classname,
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
    newProc.setLineInfo(createMethod.lineInfoObj)
    initProc.setLineInfo(createMethod.lineInfoObj)
    result.add(initProc)
  result.add(newProc)


proc createInitVTable(classname: string, initlines: NimNode): NimNode {.compiletime.} =
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
        ident classname,
        newEmptyNode()
      )
    ),
    newEmptyNode(),
    newEmptyNode(),
    initlines
  )


proc createType(classname: string, basename: string, body: NimNode): (NimNode, NimNode) =
  var reclist = newNimNode(nnkRecList)
  var methods: seq[NimNode]
  var initLines = newStmtList()
  var hasDestructor = false
  var constructor: NimNode = nil
  if basename.len > 0:
    initLines.add(
      newCall("initVT",
        nnkCast.newTree(
          ident basename,
          ident "self"
        )
      )
    )
  for elem in body.children:
    case elem.kind
    of nnkVarSection, nnkLetSection:
      # Variable definition
      reclist.addVarNode(elem)
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
      let procname = elem.getProcName()
      if procname == "=destroy":
        # Create destructor method
        hasDestructor = true
        methods.insert(createDestroyMethod(classname, elem), 0)
      elif procname == "=new":
        # Create constructor method
        constructor = createCreateMethod(classname, elem)
      else:
        let il = addProcNode(methods, classname, basename, elem, reclist)
        if il.len > 0:
          for ill in il:
            initLines.add(ill)
    of nnkProcDef:
      ## Non-virtual method
      ## - just add the proc to the statement list and set lineInfoObj to it
      let procname = elem.getProcName()
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

  ## For destructorless classes just create ref object
  ## For classes with destructor, create class object and a class ref object
  var theType: NimNode = nnkTypeSection.newTree()
  if hasDestructor:
    let cobj = (classname & "Obj").ident
    theType.add(
      nnkTypeDef.newTree(
        nnkPostfix.newTree(
          ident "*",
          ident classname
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
    theType.add(
      nnkTypeDef.newTree(
        nnkPostfix.newTree(
          ident "*",
          ident classname
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
  methods.add(createInitVTable(classname, initLines))
  if constructor.isNil:
    methods.add(createCreateMethod(classname, nil))
  else:
    methods.add(constructor)
  result = (theType, newStmtList(methods))


macro class*(head, body: untyped): untyped =
  let (classname, basename) = getNameAndBase(head)
  result = newStmtList()
  let cacheItem = TCacheItem(basename: basename)
  if classCache.hasKey(classname):
    when defined(nimsuggest):
      classCache.del(classname)
    else:
      error("Duplicate class " & classname, head)
  classCache[classname] = cacheItem
  let (typeNode, methods) = createType(classname, basename, body)
  typeNode.setLineInfo(head.lineInfoObj)
  result.add(typeNode)
  result.add(methods)
  #echo result.repr


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
