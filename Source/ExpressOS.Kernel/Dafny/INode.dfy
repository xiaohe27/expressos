class Data {}
class INode 
{
ghost var tailContents: seq<Data>;
ghost var footprint: set<INode>;

var data: Data;
var next: INode;

predicate good()
reads this, footprint;
{
    this in footprint 
	&& (next != null ==> (next in footprint 
	&& this !in next.footprint 
	&& footprint == {this} + next.footprint
	&& tailContents == [next.data] + next.tailContents
	))
	&& (next ==null ==> tailContents == [] && footprint == {this})
}

predicate Valid()
reads this, footprint;
{
    good() && (next != null ==> next.Valid())
}


predicate lenLemma()
requires Valid();
reads this, footprint;
ensures lenLemma();
ensures |footprint| == |tailContents| + 1;
{
if (next == null) then footprint == {this}
						&& tailContents == []
else footprint == {this} + next.footprint &&
	 tailContents == [next.data] + next.tailContents
		&& next.lenLemma()
}


predicate nextI(stepNum:int, node:INode)
requires Valid();
requires 0 <= stepNum <= |tailContents|;
reads this, footprint;
{
if stepNum == 0 then this == node
else next != null && next.nextI(stepNum-1, node)
}

predicate nextContentLemma(stepNum:int, node:INode)
requires Valid();
requires 0 <= stepNum <= |tailContents|;
requires nextI(stepNum, node);
reads this, footprint;
ensures node != null;
ensures nextContentLemma(stepNum, node);
ensures stepNum == 0 ==> node.data == data;
ensures stepNum > 0 ==> (node.data == tailContents[stepNum-1]);
{
if stepNum == 0 then nextI(0, node)
else tailContents == [next.data] + next.tailContents
&& next.nextContentLemma(stepNum-1, node)
}

/*
predicate nextILemma(stepNum:int, node:INode)
requires Valid();
requires node != null && node.Valid();
requires node in footprint;
reads this, footprint;
ensures nextI(stepNum, node);
{
}
*/

/*
predicate ValidLemma()
requires Valid();
reads this, footprint;
ensures ValidLemma();
ensures forall nd :: nd in footprint ==> nd != null && nd.footprint <= footprint;
{
if next == null then (footprint == {this})
else (
footprint == {this} + next.footprint
&& next.ValidLemma())
}

predicate allVLemma()
requires Valid();
reads this, footprint;
ensures allVLemma();
ensures forall nd :: nd in footprint ==> nd != null && nd.Valid();
{
next != null ==> next.allVLemma()
}
*/


constructor init(d:Data) 
modifies this;
ensures Valid();
ensures data == d;
ensures next == null;

ensures footprint == {this};
ensures tailContents == [];
ensures fresh(footprint - {this});
{
    data := d;
	next := null;
    tailContents := [];
	footprint := {this};
}

/*
method preAppend(d:Data) returns (node:INode)
requires Valid();
ensures node != null && node.Valid();
ensures node.data == d && node.next == this;
ensures node.tailContents == [this.data] + this.tailContents;
{
var r := new INode.init(d);
r.next := this;

r.footprint := r.footprint + this.footprint;
r.tailContents := [this.data] + this.tailContents;
return r;
}

method append(d:Data)
requires Valid();

modifies footprint;
decreases footprint;
ensures Valid();
ensures (tailContents == old(tailContents) + [d]);
ensures this.data == old(this.data);
ensures fresh(footprint - old(footprint));
{
var node := new INode.init(d);

if(next == null)
{
next := node;
this.tailContents := [d];
}

else
 {
next.append(d);
this.tailContents := [this.next.data] + this.next.tailContents;
}

this.footprint := {this} + next.footprint;

}

method insertAt(i:int, d:Data)
requires 0 < i <= |tailContents|;
requires Valid();
modifies footprint;
ensures Valid();
ensures this.data == old(this.data);
ensures tailContents == old(tailContents[0..i-1]) + [d] + old(tailContents[i-1..]);
ensures fresh(footprint - old(footprint));
{
var newNd := new INode.init(d);

if (i == 1) {
newNd.next := next;
newNd.tailContents := tailContents;
newNd.footprint := {newNd} + next.footprint;

assert newNd.tailContents == old(tailContents[i-1..]);
assert newNd.Valid();

this.next := newNd;
}

else {
next.insertAt(i-1, d);
}

this.tailContents := [next.data] + next.tailContents;

assert tailContents == old(tailContents[0..i-1]) + [d] + old(tailContents[i-1..]);

this.footprint := {this} + next.footprint;
}
*/

////////////////////////////////////////////////////////
/*
method update(d:Data, index:int)
requires 0 <= index <= |tailContents|;
requires Valid();
modifies footprint;
ensures Valid();
ensures index == 0 ==> (data == d && tailContents == old(tailContents));
ensures index > 0 ==> (this.data == old(this.data)
&& tailContents == old(tailContents[0..index-1]) + [d] +
						old(tailContents[index..]));
ensures footprint == old(footprint);
{
if (index == 0) {data := d; }
else {
next.update(d, index-1);
tailContents := [next.data] + next.tailContents;
}
}
*/


}


class INodes {
  var head: INode;

  ghost var contents: seq<Data>;
  ghost var footprint: set<object>;
  ghost var spine: set<INode>;

predicate valid()
reads this, footprint; 
{
this in footprint 
&& spine <= footprint
&& head in spine 
&&
(forall nd :: nd in spine ==> (nd != null && nd.footprint <= footprint - {this})) 
&&
(forall nd :: nd in spine ==> nd != null && nd.Valid())

&&
(forall nd :: nd in spine ==> (nd.next != null ==> nd.next in spine))

&& contents == head.tailContents
}


method init()
modifies this;
ensures valid() && fresh(footprint - {this});
ensures |contents| == 0;
ensures spine == {head};
ensures head.next == null;
{
head := new INode.init(null);

contents := head.tailContents;

footprint := {this};
footprint := footprint + head.footprint;
spine := {head};
}

/*
method len() returns (len:int)
requires valid();
ensures valid();
ensures len == |contents|;
{
var tmp:INode;
tmp := head;
len := 0;

while(tmp.next != null)
decreases tmp.footprint;
invariant tmp != null && tmp.Valid();
invariant tmp.next == null ==> tmp.tailContents == [];
invariant len + |tmp.tailContents| == |contents|;
{
len := len + 1;

tmp := tmp.next;
}

}
*/


/*
method get(index:int) returns (d:Data)
requires valid();
requires 0 <= index < |contents|;

//ensures valid();
//ensures d == contents[index];
{
var curNd: INode;
var curPos: int;

curNd := head;
curPos := 0; 

while (curNd.next != null)
decreases curNd.footprint;
invariant 0 <= curPos <= index;
invariant head.Valid();
invariant curNd != null && curNd.Valid() && head.nextContentLemma(curPos, curNd);
//invariant curNd.next != null ==>
//	curNd.next.data == head.tailContents[curPos];
{
if (curPos == index) 
{
return curNd.next.data;
}

curPos := curPos + 1;
curNd := curNd.next;
}

}
*/


/*
method add2Front(d:Data)
modifies footprint;
requires valid();
requires d != null;

ensures valid();
ensures contents == [d] + old(contents);
ensures fresh(footprint - old(footprint));
{

var newNd := new INode.init();
newNd.data := d;
newNd.next := head.next;

newNd.tailContents := (if (newNd.next == null) then [] else [newNd.next.data] + newNd.next.tailContents);
newNd.footprint := newNd.footprint + (if (newNd.next == null) then {} else newNd.next.footprint);

head.next := newNd;
head.footprint := head.footprint + {newNd};
head.tailContents := [d] + head.tailContents;

this.footprint := this.footprint + {newNd};

this.spine := this.spine + {newNd};

this.contents := head.tailContents;

}

method insert(d:Data, pos:int) 
modifies footprint;
requires valid();
requires d != null;
//requires 0 <= pos <= |contents|;
requires pos == 0;

ensures valid();
ensures |contents| == (|old(contents)| + 1);
ensures fresh(footprint - old(footprint));
{
//assume pos == 0;

var length := this.len();
if (pos == 0) {

add2Front(d);
}

else if (pos == length) {}

else {}
}
*/

}


