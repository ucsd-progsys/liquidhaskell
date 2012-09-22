(*
 * Copyright © 1990-2002 The Regents of the University of California. All rights reserved. 
 *
 * Permission is hereby granted, without written agreement and without 
 * license or royalty fees, to use, copy, modify, and distribute this 
 * software and its documentation for any purpose, provided that the 
 * above copyright notice and the following two paragraphs appear in 
 * all copies of this software. 
 * 
 * IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY 
 * FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES 
 * ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN 
 * IF THE UNIVERSITY OF CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY 
 * OF SUCH DAMAGE. 
 * 
 * THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES, 
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY 
 * AND FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS 
 * ON AN "AS IS" BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION 
 * d 
 * TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 *
 *)

{
  module E = Errorline
  open E
  open HornParse 
	       
  let lexerror msg lexbuf = 
    E.error (Lexing.lexeme_start lexbuf) msg
      
}

let letdig   = ['0'-'9' 'a'-'z' 'A'-'Z' '_' '@' ''' '.' '#']
let small    = ['a'-'z']
let digit    = ['0'-'9']

rule token = parse
    ['\r''\t'' ']       { token lexbuf}
  | '\n'		{ begin
			    E.startNewline (Lexing.lexeme_end lexbuf);
			    token lexbuf 
			  end }
  | "//"[^'\n']*'\n'
                        { begin
                            E.startNewline (Lexing.lexeme_end lexbuf);
			    token lexbuf
                          end }
  | '['                 { LB }
  | ']'                 { RB }
  | '('			{ LPAREN }
  | ')'			{ RPAREN }
  | '{'			{ LC }
  | '}'			{ RC }
  | '~'                 { NOT }
  | ';'                 { SEMI }
  | ','                 { COMMA }
  | ':'                 { COLON }
  | '+'                 { PLUS }
  | '-'                 { MINUS }
  | '*'                 { TIMES }
  | '/'                 { DIV }
  | '.'                 { DOT }
  | "hc"                { HC }
  | "Bexp"              { BEXP }
  | "false"             { FALSE }
  | "true"              { TRUE }
  | "&&"                { AND }
  | "||"                { OR  }
  | "!="		{ NE }
  | "="		        { EQ }
  | "=<"		{ LE }
  | "<"		        { LT }
  | ">="		{ GE }
  | ">"		        { GT }
  | "->"                { IMPL }
  | (digit)+	        { let str = Lexing.lexeme lexbuf in
			  let len = String.length str in
			  let zero = Char.code '0' in
			  let rec accum a d =
			    let acc c = a + (d * ((Char.code c) - zero)) in
			    function
			      0 -> let c = str.[0] in
				   if c='-' then - a else (acc c)
			    | i -> accum (acc str.[i]) (d * 10) (i - 1)
			  in
			  Num (accum 0 1 (len-1)) }
  
  | '_'(digit)+ 	{ Id (Lexing.lexeme lexbuf) }
  | (small)letdig+      { Var (Lexing.lexeme lexbuf) } 
  | eof			{ EOF }
  | _			{ 
                          begin
                            lexerror ("Illegal Character '" ^ 
                                      (Lexing.lexeme lexbuf) ^ "'") lexbuf;
			    token lexbuf
			  end }

