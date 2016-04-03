

//------------------Project 1-------------------------------------
//---------------------------------------------------------------
//------------Philipp Schimmelfennig -Panuya Balasuntharam------------
//---------------------------------------------------------------

sig LinearProgram{
	function: some Function,
	mainFunction: one MainFunction
}

fact {
	#LinearProgram = 1
}

--------------------------Type---------------------------------------------
---------------------------------------------------------------------------

sig Type {
	isSubTypeOf: lone Type
}


sig Function {
	returnType: one Type, 
	formalParameters: set FormalParameter,
	belongsToOneLinPr: one LinearProgram, 
	sequence: one  LinearSequenceOfStatement
}

sig MainFunction extends Function{}


fact belongsToFunction{
	all f: Function | all l:LinearProgram | l in f.belongsToOneLinPr <=> f in l.function 
}

fact mainFunctionHasNoParameter{
	all m: MainFunction | m.formalParameters = none
}

fact mainFunctionBelongsToAFunction{
	all m: MainFunction | all p: LinearProgram | p.mainFunction = m <=> m.belongsToOneLinPr = p
}

fact sequenceIsReverseOfBelongsTo{
	all f: Function | all x: LinearSequenceOfStatement | f.sequence = x <=> x.belongsTo = f
}

fact avoidRecursion{
	all f: Function| f.*(sequence.statements.expression.calledFunction) != f
}



-------------------------Parameter-----------------------------------.------
---------------------------------------------------------------------------
abstract sig Parameter {
	type: one Type
}

sig FormalParameter extends Parameter{
	belongsTo: one Function,
	belongsToOneVariable: one Variable
}

sig ActualParameter extends Parameter {
	expression: one Expr
}


fact FormalParameter{
	all f: Function | all p: FormalParameter | f.formalParameters = p <=> p.belongsTo = f
}


--------------------------Statement-----------------------------------------
---------------------------------------------------------------------------

sig LinearSequenceOfStatement {
	belongsTo: one Function,
	firstStatement: one Statement,
	lastStatement: one ReturnStatement,
	statements: some Statement
}

abstract sig Statement {
	nextStatement: lone Statement,
	expression: lone Expr,
	belongsToLinSeq: one LinearSequenceOfStatement 
}

sig AssignementStatement  extends Statement{
	var: one Variable,
	expressions: one Expr
}

sig ReturnStatement extends Statement{}


-----------------------------------------------

--fact{#LinearSequenceOfStatement = 1}

fact{#AssignementStatement >1}


fact {
   all s:Statement | all x: LinearSequenceOfStatement | (s.belongsToLinSeq = x) => s in x.statements
}

// First- and LastStatement should 
fact{
	all x: LinearSequenceOfStatement |  (x.lastStatement in x.statements) && (x.firstStatement in x.statements)
}


--TODO: Next 3 facts doesn't work
--ProblemToSolve: A Statement need to pointed just by one LinearSequence

fact {
	--all s:Statement | all disj x1, x2: LinearSequenceOfStatement | (s in x1.statements => s not in x2.statements ) 
}

fact {
--	all s:Statement | all disj x1, x2: LinearSequenceOfStatement | (x1.lastStatement = s => x2.lastStatement !=s)  
}

fact {
--	all s:Statement | all disj x1, x2: LinearSequenceOfStatement | (x1.firstStatement = s => x2.firstStatement !=s)  
}


// A Statement and its NextStatement should belong to the same Linear Sequence
fact {
	all disj s1, s2: Statement | all x: LinearSequenceOfStatement | (s1.nextStatement = s2) && (s1.belongsToLinSeq = x) => (s2.belongsToLinSeq = x)
}

// All Statements need to pointed by a LinearSequence
fact allStatementMustAppear{
	all s: Statement | some x: LinearSequenceOfStatement  | s in x.statements
}

// Avoid Circle of NextStatements
fact noCircle{
	all disj s1, s2: Statement | s1.nextStatement = s2 => s1 not in s2.^nextStatement
}

/*
fact expressionMustAppearInStatement {
	all e: Expr | some s: Statement | e in s.expression
}

*/

// FirstStatement doesn't have a predecessor  
fact firstStatement {
	all disj s1, s2: Statement | all x: LinearSequenceOfStatement  |(s2 = x.firstStatement) => (s1.nextStatement ! = s2)  
}

// ReturnStatement has no NextStatement and the others need to have one
fact lastStatementReturnstatement{
	(all r: ReturnStatement | r.nextStatement = none) && (all a: AssignementStatement |# a.nextStatement = 1) && (all v: VarDecl |# v.nextStatement =1)
}

 // A Statement cannot be NextStatement of itself
fact notReflexivNextStatement{
	all s:Statement | s.nextStatement != s
}

// Two Statements have different NextStatements
fact differentNextStatement {
	all disj s1, s2, s3: Statement | s1.nextStatement = s2 => s3.nextStatement != s2
}

// 
fact{
	all a: AssignementStatement |  p_subtypeOf [a.variable.type, a.expression.type]
}


------------------------------------------------------------------

sig Expr {
	type: one Type,
	children: set Expr,
	parent: lone Expr,
	statement: lone Statement
}

sig Literal extends Expr {}

sig CallExpression extends Expr {
	calledFunction: one Function,
	actualParameter: set ActualParameter
}


fact {
	all e: Expr| e.statement = none <=> e.parent != none
}

fact canNotConsistItself{
	all e: Expr | (e not in e.^children) && (e != e.parent)
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
	declared: one Bool, 
	readIn: some Expr,
	assigned: one Bool
}


sig VariableReference extends Expr{
	fvariable: lone FormalParameter,
	avariable: lone Variable
}

sig VarDecl extends Statement{
	type: one Type,
	variable: one Variable
} 


fact onlyOneVariableReference {
	all v: VariableReference | all f: FormalParameter | all a: Variable| (f in v.fvariable => a not in  v.avariable) && (a in  v.avariable => f not in v.fvariable)
}

sig Bool extends Type{}


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

--------- Predicates —------------


pred p_ContainsCall [f: Function] {
 some x: CallExpression | x in f.sequence.statements.expression
}

pred p_isAssigned [v: Variable] {
 some f: Function | some s:AssignementStatement | s in f.sequence.statements && v in s.var
}


pred p_isRead [v: Variable] {
 some e: VariableReference | v in e.avariable // TODO
}


pred p_isDeclared [v: Variable] {
 some f: Function | some s: VarDecl | s in f.sequence.statements && v in s.variable
}

pred p_subtypeOf [t1: Type, t2: Type] {
 t1 in t2.*isSubTypeOf
}



pred p_assignsTo [s: Statement, vd: VarDecl] {
	vd.variable in s.var
}



pred show { 
	all u: Function | p_ContainsCall [u] 
}


run show
