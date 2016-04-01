

//------------------Project 1-------------------------------------
//---------------------------------------------------------------
//------------Philipp Schimmelfennig -Panuya Balasuntharam------------
//---------------------------------------------------------------

abstract sig LinearProgram{
	function: some Function,
	mainFunction: one MainFunction
}


--------------------------Type-------------------------------------

sig Type {
	superType: lone Type
}


sig Function {
	returnType: one Type, 
	formalParameters: set FormalParameter,
	belongsToOneLinPr: one LinearProgram, 
	sequence: one  LinearSequenceOfStatement
}

sig MainFunction extends Function{

}


fact belongsToFunction{
	all f: Function | all l:LinearProgram | f.belongsToOneLinPr = l <=> l.function = f
}


fact avoidRecursion{
	
}

-------------------------Parameter--------------------------------

abstract sig Parameter {
	type: one Type
}

sig FormalParameter extends Parameter {
	belongsTo: one Function,
	belongsToOneVariable: one Variable
}

sig ActualParameter extends Parameter {}


fact reflexitivFormalParameter{
	all f: Function | all p: FormalParameter | f.formalParameters = p <=> p.belongsTo = f
}


--------------------------Statement-----------------------------

sig LinearSequenceOfStatement {
	belongsTo: one Function,
	firstStatement: one Statement,
	lastStatement: one ReturnStatement,
	statements: some Statement
}

abstract sig Statement {
	nextStatement: lone Statement,
	expression: lone Expr
}

sig AssignementStatement  extends Statement{
	variable: one DeclaredVariable
}

sig ReturnStatement extends Statement{
	belongsTo:  one Function,
	isIn: one LinearSequenceOfStatement
}

fact lastStatementIsReturnStatement {
	all s: Statement | all o: LinearSequenceOfStatement | s not in o.lastStatement.nextStatement
}



fact allStatementMustAppear{
	all a: AssignementStatement |all s: LinearSequenceOfStatement  |a in s.statements
}

fact noCircle{
	all s1, s2: Statement | s1.nextStatement = s2 => s1 not in s2.^nextStatement
}

fact expressionMustAppearInStatement {
	all e: Expr | all s: Statement | e in s.expression
}

fact statement{
 all s: LinearSequenceOfStatement |all x: Statement | x in s.statements <=> x in (s.firstStatement.^nextStatement + s.firstStatement)
} 

fact noItSelf{
	all s:Statement | s.nextStatement != s
}

fact differentNextStatement {
	all s1, s2, s3: Statement | s1.nextStatement = s2 => s3.nextStatement != s2
}


------------------------------------------------------------------

sig Expr {
  type: one Type,
  children: set Expr,
  parent: lone Expr     
}

sig Literal extends Expr {}

sig CallExpression extends Expr {
	calledFunction: one Function
}



---------------------------Expression Tree-----------------------
sig Node {
	parent: lone Node,
	children: set Node,
	exprTree: one ExpressionTree
}

sig ExpressionTree {
	root: one Node,
	leaves: set Node
}



fact parentChildrenRelationsship{
	all n1, n2: Node | n1. parent = n2  <=> n1 in n2.children 
}


// unsicher ob dies funktioniert. Ich möchte root definieren
fact root{
	(all r: ExpressionTree | all n: Node | r.root in n.^parent)&&
	(all r: ExpressionTree | all n: Node | r. root not in n.^children)
}

fact notSameRootAndLeaves{
	all e: ExpressionTree | e.root not in e.leaves
}

fact notOwnChild {
	all n: Node | n not in n.children
}

fact notOwnParent{
	all n: Node | n not in n.parent
}

fact notSameRoot{
	all e1, e2: ExpressionTree | e1.root != e2.root
}

fact parentAndChildHasTheSameExprTree {
	all n1, n2: Node | n1.parent = n2 => n1.exprTree = n2.exprTree
}



-------------------------------Variable-----------------------------------------

sig Variable {
	declaredVariables: set DeclaredVariable,
	formalParameters: set FormalParameter, 
	assignedVariables: set AssignedVariable,
	belongsToOneFunction: one Function
}

sig VariableReference extends Expr{
	fvariable: lone FormalParameter,
	avariable: lone AssignedVariable
}


sig DeclaredVariable {
	type: one Type,
	belongsTo: one Variable	
}

sig AssignedVariable extends DeclaredVariable {
	readIn: some Expr,
}


sig VarDecl extends Statement{
	type: one Type
} // in UML we call it DeclarationStatement


fact onlyOneVariableReference {
	all v: VariableReference | all f: FormalParameter | all a: AssignedVariable| (f in v.fvariable => a not in  v.avariable) && (a in  v.avariable => f not in v.fvariable)
}

fact variablelist{
	(all d: DeclaredVariable | all v: Variable | d in v.declaredVariables <=> d.belongsTo = v) &&
	(all p: FormalParameter | all v: Variable | p in v.formalParameters  <=> p.belongsToOneVariable = v) 
}


//----------------------Functions--------------------------------

fun p_numFunctionCalls[]: Int {
  # CallExpression
}

fun p_expressionTypes[]:set Type {
  Expr.type
}

fun p_literalTypes[]:set Type {
  Literal.type
}

fun p_statementsInFunction [f: Function]: set Statement {
  f.sequence.statements
}

fun p_statementsAfter [s: Statement]: set Statement {
  s.*nextStatement
}

fun p_parameters [f: Function]: set FormalParameter {
  f.formalParameters
}

fun p_subexpr [e: Expr]: set Expr {
  e.children
}


-- Predicates --------------


pred p_ContainsCall [f: Function] {
  some x: Expr | x in f.sequence.statements.expression
}

/*
pred p_isAssigned [v: Variable] {
  some f: Function | some s:AssignementStatement | s in f.sequence.statements && s.variable = v
}
*/
pred p_isRead [v: Variable] {
  some e: VariableReference | e.read = v
}


pred p_isDeclared [v: Variable] {
  some f: Function | some s:DeclarationStatemente | s in f.sequence.statements && s.variable = v


pred p_isSubtype [t1: Type, t2: Type] {
  t1 in t2.^superType
}

pred p_assignsTo [s: Statement, vd: VarDecl] {
  s.variable = vd.variable
}


pred show {}

run show for 3
