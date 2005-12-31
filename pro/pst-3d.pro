%%
%% This is file `pst-3d.pro',
%% generated with the docstrip utility.
%%
%% The original source files were:
%%
%% pst-3d.dtx  (with options: `prolog')
%% 
%% IMPORTANT NOTICE:
%% 
%% For the copyright see the source file.
%% 
%% You are *not* allowed to modify this file.
%% 
%% You are *not* allowed to distribute this file.
%% For distribution of the original source see the terms
%% for copying and modification in the file pst-3d.dtx.
%% 
/tx@Pst3dDict 20 dict def
tx@Pst3dDict begin
%
/SetMatrixThreeD {
  dup sin /e ED cos /f ED
  /p3 ED /p2 ED /p1 ED
  p1 0 eq
  { /a 0 def /b p2 0 le { 1 } { -1 } ifelse def
    p3 p2 abs
  }
  { p2 0 eq
    { /a p1 0 lt { -1 } { 1 } ifelse def /b 0 def
      p3 p1 abs
    }
    { p1 dup mul p2 dup mul add sqrt dup
      p1 exch div /a ED
      p2 exch div neg /b ED
      p3 p1 a div
    }
    ifelse
  }
  ifelse
  atan dup sin /c ED cos /d ED
  /Matrix3D
  [
    b f mul c a mul e mul sub
    a f mul c b mul e mul add
    d e mul
    b e mul neg c a mul f mul sub
    a e mul neg c b mul f mul add
    d f mul
  ] def } def
%
/ProjThreeD {
  /z ED /y ED /x ED
  Matrix3D aload pop
  z mul exch y mul add exch x mul add
  4 1 roll
  z mul exch y mul add exch x mul add
  exch } def 
%
/SetMatrixEmbed {
  SetMatrixThreeD
  Matrix3D aload pop
  /z3 ED /z2 ED /z1 ED /x3 ED /x2 ED /x1 ED
  SetMatrixThreeD
  [
  Matrix3D aload pop
  z3 mul exch z2 mul add exch z1 mul add 4 1 roll
  z3 mul exch z2 mul add exch z1 mul add
  Matrix3D aload pop
  x3 mul exch x2 mul add exch x1 mul add 4 1 roll
  x3 mul exch x2 mul add exch x1 mul add
  3 -1 roll 3 -1 roll 4 -1 roll 8 -3 roll 3 copy
  x3 mul exch x2 mul add exch x1 mul add 4 1 roll
  z3 mul exch z2 mul add exch z1 mul add
  ] concat } def
%
/TMSave {
  tx@Dict /TMatrix known not { /TMatrix { } def /RAngle { 0 } def } if
  /TMatrix [ TMatrix CM ] cvx def } def
%
/TMRestore { 
  CP /TMatrix [ TMatrix setmatrix ] cvx def moveto } def
%
/TMChange {
  \tx@TMSave
  /cp [ currentpoint ] cvx def % ??? Check this later.
  CM
% Set "standard" coor. system , with "pt" units and origin at currentpoint.
% This let's us rotate, or whatever, around \TeX's current point, without
% having to worry about strange coordinate systems that the dvi-to-ps
% driver might be using.
  CP T \tx@STV
% Let M = old matrix (on stack), and M' equal current matrix. Then
% go from M' to M by applying  M Inv(M').
  CM matrix invertmatrix    % Inv(M')
  matrix concatmatrix       % M Inv(M')
% Now modify transformation matrix:
  exch exec
% Now apply M Inv(M')
  concat cp moveto } def
%
end

