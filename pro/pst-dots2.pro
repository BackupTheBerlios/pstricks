%!
%% PostScript prologue for pstricks2.tex.
%% Version 2.00, 2004/12/18
%% For distribution, see pstricks.tex.
%%
%% Timothy Van Zandt <tvz@Princeton.EDU>
%%
%% Modified by Etienne Riga  - Dec. 16, 1999
%% Modified by Etienne Riga  - 2004/07/25 (er)
%% to add /Diamond, /SolidDiamond and /BoldDiamond
%% Modified by Herbert Voss (hv) - 2004/12/27 
%
10 dict dup begin
  /FontType 3 def
  /FontMatrix [ .001 0 0 .001 0 0 ] def
%-------------- hv begin 2004/07/25   from: AVK ++   2003/03/24
  /FontBBox [ -571.5 -742.5 571.5 574.7 ] def
%  /FontBBox [ 0 0 0 0 ] def
%-------------- hv end AVK --
  /Encoding 256 array def
  0 1 255 { Encoding exch /.notdef put } for
  Encoding
    dup (b) 0 get /Bullet put
    dup (c) 0 get /Circle put
    dup (C) 0 get /BoldCircle put
    dup (u) 0 get /SolidTriangle put
    dup (t) 0 get /Triangle put
    dup (T) 0 get /BoldTriangle put
    dup (r) 0 get /SolidSquare put
    dup (s) 0 get /Square put
    dup (S) 0 get /BoldSquare put
    dup (q) 0 get /SolidPentagon put
    dup (p) 0 get /Pentagon put
    dup (P) 0 get /BoldPentagon put
%-------------- hv begin 2004/07/25   from: er 2003/03/24
    dup (k) 0 get /Asterisk put
    dup (K) 0 get /BoldAsterisk put
    dup (J) 0 get /SolidAsterisk put
    dup (h) 0 get /Hexagon put
    dup (H) 0 get /BoldHexagon put
    dup (G) 0 get /SolidHexagon put
    dup (a) 0 get /Add put
    dup (A) 0 get /BoldAdd put
    dup (x) 0 get /Mul put
    dup (X) 0 get /BoldMul put
    dup (m) 0 get /Oplus put
    dup (M) 0 get /BOplus put
    dup (e) 0 get /SolidOplus put
    dup (n) 0 get /Otimes put
    dup (N) 0 get /BOtimes put
    dup (E) 0 get /SolidOtimes put
    dup (i) 0 get /Bar put
    dup (I) 0 get /BoldBar put
    dup (l) 0 get /SolidDiamond put
    dup (d) 0 get /Diamond put
        (D) 0 get /BoldDiamond put
  /Metrics 34 dict def
%  /Metrics 13 dict def
%-------------- hv end er --
  Metrics begin
    /Bullet 1000 def
    /Circle 1000 def
    /BoldCircle 1000 def
    /SolidTriangle 1344 def
    /Triangle 1344 def
    /BoldTriangle 1344 def
    /SolidSquare 886 def
    /Square 886 def
    /BoldSquare 886 def
    /SolidPentagon 1093.2 def
    /Pentagon 1093.2 def
    /BoldPentagon 1093.2 def
%-------------- hv begin 2004/07/25   from: er 2003/03/24
    /SolidHexagon 1000 def
    /Hexagon 1000 def
    /BoldHexagon 1000 def
    /Asterisk 1000 def
    /BoldAsterisk 1000 def
    /SolidAsterisk 1000 def
    /Add 1000 def
    /BoldAdd 1000 def
    /Mul 1000 def
    /BoldMul 1000 def
    /Oplus 1000 def
    /BOplus 1000 def
    /SolidOplus 1000 def
    /Otimes 1000 def
    /BOtimes 1000 def
    /SolidOtimes 1000 def
    /Bar 1000 def
    /BoldBar 1000 def
    /SolidDiamond 1008 def
    /Diamond 1008 def
    /BoldDiamond 1008 def
%-------------- hv end er --
    /.notdef 0 def
  end
%-------------- hv begin 2004/07/25   from: er 2003/03/24
  /BBoxes 34 dict def
%  /BBoxes 13 dict def
%-------------- hv end er --
  BBoxes begin
    /Circle { -550 -550 550 550 } def
    /BoldCircle /Circle load def
    /Bullet /Circle load def
    /Triangle { -571.5 -330 571.5 660 } def
    /BoldTriangle /Triangle load def
    /SolidTriangle /Triangle load def
    /Square { -450 -450 450 450 } def
    /BoldSquare /Square load def
    /SolidSquare /Square load def
    /Pentagon { -546.6 -465 546.6 574.7 } def
    /BoldPentagon /Pentagon load def
    /SolidPentagon /Pentagon load def
%-------------- hv begin 2004/07/25   from: er 2003/03/24
    /Hexagon { -476 -550 476 550 } def
    /BoldHexagon /Hexagon load def
    /SolidHexagon /Hexagon load def
    /Asterisk /Circle load def
    /BoldAsterisk /Circle load def
    /SolidAsterisk /Circle load def
    /Add  /Circle load def
    /BoldAdd /Circle load def
    /Mul /Circle load def
    /BoldMul /Circle load def
    /Oplus /Circle load def
    /BOplus /Circle load def
    /SolidOplus /Circle load def
    /Otimes /Circle load def
    /BOtimes /Circle load def
    /SolidOtimes /Circle load def
    /Bar { -40 -680 40 680 } def
    /BoldBar { -60 -680 60 680 } def
    /Diamond { -428.5 -742.5 428.5 742.5 } def
    /BoldDiamond /Diamond load def
    /SolidDiamond /Diamond load def
%-------------- hv end er --
    /.notdef { 0 0 0 0 } def
  end
%-------------- hv begin 2004/07/25   from: er 2003/03/24
  /CharProcs 48 dict def
%  /CharProcs 20 dict def
%-------------- hv end er --
  CharProcs begin
    /Adjust {
      2 copy dtransform floor .5 add exch floor .5 add exch idtransform
      3 -1 roll div 3 1 roll exch div exch scale
    } def
    /CirclePath { 0 0 500 0 360 arc closepath } def
    /Bullet { 500 500 Adjust CirclePath fill } def
    /Circle { 500 500 Adjust CirclePath .9 .9 scale CirclePath eofill } def
    /BoldCircle { 500 500 Adjust CirclePath .8 .8 scale CirclePath eofill } def
    /BoldCircle { CirclePath .8 .8 scale CirclePath eofill } def
    /TrianglePath {
      0  660 moveto -571.5 -330 lineto 571.5 -330 lineto closepath
    } def
    /SolidTriangle { TrianglePath fill } def
    /Triangle { TrianglePath .85 .85 scale TrianglePath eofill } def
    /BoldTriangle { TrianglePath .7 .7 scale TrianglePath eofill } def
    /SquarePath {
      -450 450 moveto 450 450 lineto 450 -450 lineto -450 -450 lineto
      closepath
    } def
    /SolidSquare { SquarePath fill } def
    /Square { SquarePath .89 .89 scale SquarePath eofill } def
    /BoldSquare { SquarePath .78 .78 scale SquarePath eofill } def
    /PentagonPath {
      -337.8 -465   moveto
       337.8 -465   lineto
       546.6  177.6 lineto
         0    574.7 lineto
      -546.6  177.6 lineto
      closepath
    } def
    /SolidPentagon { PentagonPath fill } def
    /Pentagon { PentagonPath .89 .89 scale PentagonPath eofill } def
    /BoldPentagon { PentagonPath .78 .78 scale PentagonPath eofill } def
%-------------- hv begin 2004/07/25   from: er 2003/03/24
    /HexagonPath {0 550 moveto -476 275 lineto -476 -275 lineto
	0 -550 lineto 476 -275 lineto 476 275 lineto
	closepath } def
    /SolidHexagon { HexagonPath fill } def
    /Hexagon { HexagonPath .895 .895 scale HexagonPath eofill } def
    /BoldHexagon { HexagonPath .79 .79 scale HexagonPath eofill } def
    /AsteriskPath { 
         20 0 moveto  
         10 250
         180 500 
         0 500 curveto
        -180 500 
        -10 250                      
        -20 0 curveto closepath } def
    /Asterisk { AsteriskPath 60 rotate AsteriskPath
	60 rotate AsteriskPath 60 rotate AsteriskPath
	60 rotate AsteriskPath 60 rotate AsteriskPath fill } def
    /Basterp { 50 250 220 500 0 500 curveto
         -220 500 -50 250 -50 30 cos 100 mul curveto } def
    /BoldAsteriskPath { 50 30 cos 100 mul moveto  Basterp
         60 rotate Basterp 60 rotate Basterp
         60 rotate Basterp 60 rotate Basterp
         60 rotate Basterp closepath } def
    /BoldAsterisk { BoldAsteriskPath fill} def
    /SolidAsterisk { 500 500 Adjust CirclePath
	.9 .9 scale BoldAsteriskPath eofill } def
    /CrossPath {
	40 550 moveto -40 550 lineto -40 40 lineto -550 40 lineto
        -550 -40 lineto -40 -40 lineto -40 -550 lineto 40 -550
	lineto 40 -40 lineto 550 -40 lineto 550 40 lineto
	40 40 lineto closepath } def
    /BoldCrossPath { 
	80 550 moveto -80 550 lineto -80 80 lineto -550 80 lineto
        -550 -80 lineto -80 -80 lineto -80 -550 lineto 80 -550
	lineto 80 -80 lineto 550 -80 lineto 550 80 lineto
	80 80 lineto closepath } def
    /Add { CrossPath  fill } def
    /Mul { 45 rotate CrossPath  fill } def
    /BoldAdd { BoldCrossPath  fill } def
    /BoldMul { 45 rotate BoldCrossPath  fill } def
    /Oplus { 500 500 Adjust CirclePath .9 .9 scale CirclePath eofill
	.775 .775 scale CrossPath  fill } def 
    /SolidOplus { 500 500 Adjust CirclePath 
	.775 .775 scale BoldCrossPath  eofill } def 
    /BOplus { 500 500 Adjust CirclePath .8 .8 scale CirclePath eofill
	.775 .775 scale BoldCrossPath fill } def 
    /Otimes { 500 500 Adjust CirclePath .9 .9 scale CirclePath eofill
	45 rotate .775 .775 scale CrossPath  fill } def 
    /BOtimes { 500 500 Adjust CirclePath .8 .8 scale CirclePath eofill
	45 rotate .775 .775 scale BoldCrossPath  fill } def 
    /SolidOtimes { 500 500 Adjust CirclePath
	45 rotate .775 .775 scale BoldCrossPath eofill } def 
    /BarPath { 
	40 660 moveto -40 660 lineto -40 -660 lineto 40 -660 lineto closepath 
     } def
    /Bar { BarPath fill } def
    /BoldBarPath { 
	80 660 moveto -80 660 lineto -80 -660 lineto 80 -660 lineto closepath 
     } def
    /BoldBar { BoldBarPath fill } def
    /DiamondPath {
      0 742.5 moveto -428.5 0 lineto 0 -742.5 lineto 428.5 0 lineto closepath
%      0 660 moveto -381 0 lineto 0 -660 lineto 381 0 lineto closepath
    } def
    /SolidDiamond { DiamondPath fill } def
    /Diamond { DiamondPath .865 .865 scale DiamondPath eofill } def
    /BoldDiamond { DiamondPath .73 .73 scale DiamondPath eofill } def
%-------------- hv end er --
    /.notdef { } def
  end
  /BuildGlyph {
    exch
    begin
      Metrics 1 index get exec 0
      BBoxes 3 index get exec
      setcachedevice
      CharProcs begin load exec end
    end
  } def
  /BuildChar {
    1 index /Encoding get exch get
    1 index /BuildGlyph get exec
  } bind def
end
/PSTricksDotFont exch definefont pop

