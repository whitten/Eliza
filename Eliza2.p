code stolen from: http://www.cs.bham.ac.uk/research/projects/poplog/eliza/cgi-bin/eliza2.p

/* --- Copyright University of Birmingham 2014. All rights reserved. ------
 > File:            $poplocal/local/lib/eliza2.p
 > File:            $poplocal/local/ftp/eliza/cgi-bin/eliza2.p
 > Purpose:         Local version of the system elizaprog reads one line only
 >                  Converted to output html where appropriate.
 > Author:          Aaron Sloman, 17 Sep 2002 (see revisions)
 > Documentation:
 > Related Files:   LIB elizaprog
 */


/*  BASED ON the original PDP11/40 pop-11 version:
 >  File:           C.all/lib/lib/elizaprog.p
 >  Purpose:        Sussex Mini ELIZA programme
 >  Author:         Mostly A.Sloman 1978 (see revisions)
 >  Documentation:  TEACH * ELIZA
 >  Related Files:  LIB * ELIZAPROG and the saved image.
 */

;;; Modified Aaron Sloman 24 Sep 2002
;;; for one-shot use on internet. Changed rule format to define :newrule <name>

;;; NOTES:
;;; The function changeperson is called before any tests are carried out,
;;; so that "you" always refers to the user, "I" to the computer, etc.,
;;; in the transformed sentence, which is then analysed by other procedures
;;; trying to react to it.

;;; The variable "sentence" is local to eliza, and used non-
;;; locally by other procedures. Thus, general purpose matching procedures
;;; can be defined which simply take a pattern as argument. Examples are
;;; the procedures:  itmatches, itcontains, ithasoneof, itslikeoneof,
;;;   and itsaquestion,
;;; which are used by lots of other procedures to test the current sentence.
;;; occasions.

section;

uses teaching;

compile_mode:pop11 +varsch +constr;

uses shuffle;

global vars eliza_debug = false;

vars procedure eliza2;


;;; The following could be cleaned up if we switch to using lvars with
;;; the pattern prefix "!". But the Pop11 Eliza predates the pattern prefix.

;;; Global variables used below. If possible rules should use only these
vars list, Word1, Word2, L, L1, L2, L3, ;;; pattern variables
    sentence;               ;;; NB sentence is used non-locally

;;; a table, and some procedures for transforming the input sentence
;;; so that "I" becomes "you", etc. A minor problem is coping with
;;; "are". "you are" should become "i am", whereas in "we are", "they are"
;;; "are" should be left unaltered.
;;; a further difficulty is deciding whether "you" should become "I" or "me".
;;; This program uses the simple test that I at the end of the sentence is
;;; unacceptable.
;;; The transformation goes in three stages.
;;;   first find second person occurrences of "are" and mark them.
;;;   then transform according to the table below,
;;;   then replace final "I" with "me".

lconstant

    transformtable =
    [
        [i you]
        [you i]
        [my your]
        [yourself myself]
        [myself yourself]
        [your my]
        [me you]
        [mine yours]
        [yours mine]
        [am are]
        [Are am]
        [id you had]
        [youd i had]
        [theyre they are]
        [youre  i am]
        [im you are]
        [we you]    ;;; not always safe!
        [ive you have]
        [doesnt does not]
        [didnt did not]
        [youve i have]
        [isnt is not]
        [arent are not]
        [dont do not]
        [%"'don\'t'"% do not]
        [%"'don\\\'t'"% do not]
        [werent were not]
        [mustnt must not]
        [wouldnt would not]
        [shouldnt should not]
        [shant shall not]
        ;;; previously used 'cannot', but that's inserted later now
        [cant can not]
        [couldnt could not]
        [wont will not]
    ],

    willwords =
        [will must does did should can],

    quantifiers =
        [
            [anyone noone]
            [someone noone]
            [anybody nobody]
            [somebody nobody]
            [something nothing]
            [anything nothing]
        ]
;



define iswillword(word);
    member(word, willwords)
enddefine;

define eliza_lookup(word, table);
    lvars word, table;
    ;;; Return the original word if there isn't an entry in the table.
    if table == [] then
        word
    elseif word == hd(hd(table)) then
        dl(tl(hd(table)))
    else
        eliza_lookup(word, tl(table))
    endif
enddefine;


define eliza_member(word, table);
    lvars word, table;
    ;;; Return false if there isn't an entry in the table.
    if table == [] then
        false
    elseif word == hd(hd(table)) then
        dl(tl(hd(table)))
    else
        eliza_member(word, tl(table))
    endif
enddefine;



vars procedure(itcontains, itmatches, itslikeoneof);
    ;;; all defined below: used in changeperson.

;;;; NB the above procedures use "sentence" non-locally. It must not be
;;;  an lvars variable.
define changeperson(sentence) -> sentence;
    dlocal sentence;
    dlocal Word1 Word2 L, L1, L2, L3;

	;;; get rid of period at end.
    while itmatches([??L1 .]) do L1 ->sentence endwhile;

    ;;; first distinguish second person versions of "are"
    if not(itcontains("you")) then
        sentence
    elseif itmatches([??L1 you are ??L2]) then
        [^^L1 you Are ^^L2]
    elseif itmatches([??L1 are you ??L2]) then
        [^^L1 Are you ^^L2]
    else
        sentence
    endif
        -> sentence;

    ;;; now transform according to transformtable, defined above.
    maplist(sentence, eliza_lookup(%transformtable%)) -> sentence;

    ;;; Now change "I" at the end to "me".
    if itmatches([??L1 i]) then [^^L1 me] ->sentence endif;
    if itmatches([??L1 i ?]) and last(sentence) == "?" then
        [^^L1 me ?] ->sentence
    endif;

;;; sentence =>
;;; last(sentence) =>

    ;;; Now change "you shall" to "you will:
    if itmatches([you shall ??L1]) then [you will ^^L1] ->sentence endif;
    ;;; Fix "i are"
    if itmatches([??L1 i are ??L2]) then [^^L1 i am ^^L2] ->sentence endif;
    ;;; Fix "you was"
    if itmatches([??L1 you was ??L2]) then [^^L1 you were ^^L2] ->sentence endif;
    ;;; Fix "we was"
    if itmatches([??L1 we was ??L2]) then [^^L1 we were ^^L2] ->sentence endif;
    ;;; assume "i" after at least three things should be "me"
    if itmatches([??L:3 ??L1 i ??L2]) then [^^L ^^L1 me ^^L2] ->sentence endif;

    ;;; deal with 'wont someone' 'wont you' 'wont he' etc
    ;;; also didn't, shouldn't, etc.
    ;;; these translations are not accurate, but it's just eliza

    if itmatches([?Word1:iswillword not ?Word2 ??L2]) then

        ;;; see if Word2 is one of the words in quantifiers, and if
        ;;; so get its 'negative' transform
        lvars new_quantifier = eliza_member(Word2, quantifiers);

        if new_quantifier then
            [^Word1 ^new_quantifier ^^L2]

        elseif member(Word2, [you i he she they we everyone someone it]) then
            [^Word1 ^Word2 not ^^L2]
        else sentence
        endif -> sentence;
    endif;

    ;;; now replace 'can not' with cannot
    while itmatches([??L1 can not ??L2]) do
        [^^L1 cannot ^^L2] -> sentence
    endwhile;

enddefine;

;;;   ****  READING IN A SENTENCE    ****

;;; The function trimsentence below uses function changeperson to transform the sentence.
;;; It also strips off "well" and other redundant leading words.


;;; modified for eliza2
define trimsentence(sentence) -> sentence;
    dlocal sentence;

	;;; prevent line-wrap occurring
	dlocal
		poplinemax = 2000,
		poplinewidth = 2000;

    ;;; get rid of commas immediately after words, etc.

    lvars word, list;
    for list on sentence do
        front(list) -> word;
        if strmember(last(word), '.,;:') then
            allbutlast(1, word) -> front(list)
        endif
    endfor;

    ;;; get rid of "well"  and similar redundant starting words
    while length(sentence) >  1
    and
         member(hd(sentence), [well but however still and then also yes no so , .])
    do
        tl(sentence) -> sentence;
    endwhile;

    ;;; remove leading "perhaps" 30% of the time
    if length(sentence) > 1 and hd(sentence) == "perhaps" and random(100) < 30 then
        tl(sentence) -> sentence
    endif;

enddefine;



vars eliza_rules;       ;;; used to hold names of rules


;;;   **** CIRCULATING LISTS OF POSSIBILITIES ****

;;; The procedure firstolast is used to get the first element of a list, then
;;; put it on the end of the list, so that next time a different element
;;; will be the first one. This enables a stock of standard replies to
;;; be used in certain contexts without it being too obvious.
;;; an alternative would be to use function oneof, but it cannot be
;;; relied on not to be repetitive!

;;; first we need a procedure to check whether an item contains variables
;;; and if so to instantiate them
define has_variables(list) -> result;
    ;;; true if it contains "?" or "??", except of "?" is last item
    ;;; in the list
    lvars list, result = false;
    for list on list do
        if hd(list) == "??" or (hd(list) == "?" and tl(list) /== []) then
            true -> result;
            return();
        endif
    endfor;
enddefine;

define try_instantiate(answer) -> answer;
	;;; NBNBNB This will not work if lvars are used for pattern
	;;; variables. Maybe it will work with "!" prefix used
	;;; appropriately. Needs checking.
    lvars answer, item;
    if islist(answer) and has_variables(answer) then
        ;;; instantiate it
        [%
            repeat
                quitif(answer = []);
                if answer = [?] or answer = [??] then
                    "?", quitloop()
                endif;
                hd(answer) -> item;
                if item == "??" then
                    tl(answer) -> answer;
                    dl(valof(hd(answer)))
                elseif item == "?" then
                    tl(answer) -> answer;
                    valof(hd(answer))
                else
                    item
                endif;
                tl(answer) -> answer;
            endrepeat;
        %] -> answer;
    endif;
enddefine;

/*
;;; test


vars lll = [a b c d e];
vars lll = [a b];

circulate_list(lll, 3) -> lll; lll=>


*/

define circulate_list(list, n) -> newlist;
    if tl(list) == [] then list -> newlist;
    else
    repeat n times
        lvars L1 = list, prev;
        tl(list) ->> list ->prev;
        [] -> tl(L1);
        until tl(prev) == [] do tl(prev) ->prev enduntil;
        L1 -> tl(prev);
    endrepeat;
    list -> newlist;
    endif;
enddefine;

define firstolast(list) -> (first,list);
    ;;; use original list links, to minimise garbage collection.
    circulate_list(list, random(5)) -> list;
    ;;; use first item in list as answer, after instantiating variables,
    ;;; where appropriate
    ;;; changed for one-shot eliza
    try_instantiate(oneof(list)) -> first;
    ;;; circulate_list(list, 1) -> list;

enddefine;




define macro CIRCULATE;
    ;;; read a list and plant code to "circulate" it. E.g.
    ;;; CIRCULATE [[a][b][c]]
    ;;; turns into something like
    ;;; globally declare variable circ_23 initialised to have value
    ;;;     [[a][b][c]] -> circ_23;
    ;;; then plant instructions
    ;;;     firstolast(circ_23) -> circ_23;
    ;;;     Now changed to use shuffle instead
    lvars list, word = gensym("circ_");
    listread() -> list;
    popval([global vars ^word = ^list ;]);

    ;;; dl([firstolast(^word) -> ^word])

    dl([shuffle(^word) -> ^word; try_instantiate(hd(^word))])
enddefine;

;;;   ***** A COLLECTION OF MATCHING AND RECOGNISING FUNCTIONS   ****

define itmatches(L);
    lvars L;
    sentence matches L
enddefine;

define itcontains(x);
    lvars x;
    if atom(x) then
        member(x,sentence)
    else
        sentence matches [== ^^x ==]
    endif
enddefine;

;;; the function ithasoneof takes a list of words or patterns and checks whether
;;; the current sentence contains one of them

define ithasoneof(L);
    lvars L;
    if L == [] then
        false
    else
        itcontains(hd(L)) or ithasoneof(tl(L))
    endif
enddefine;

define itslikeoneof(L);
    lvars L, pattern;
    for pattern in L do
        if sentence matches pattern then return(true) endif
    endfor;
    false
enddefine;

;;;   ****  RULES FOR REACTING TO THE SENTENCE ****

;;; First we define a syntax word called newrule.
;;; It defines a new procedure and ensures that the procedure's name is
;;; added to the global list eliza_rules.
;;; This list of names is repeatedly shuffled by eliza and then the
;;; corresponding procedures tried in order, to see if one of them can
;;; produce a response to the sentence.
;;; If it produces a response other than false, then the response will be
;;; used in replyto. If there is no response then the result of the function TRY
;;; defined below, will be false, so replyto will try something else.

[] -> eliza_rules;

/*

Define a new form

    define :newrule <name>;

        <body>

    enddefine;

turns into (in effect):

    define <name>();

        <body>

    enddefine;


    <name> :: eliza_rules -> eliza_rules ;

*/


define :define_form newrule;
    lvars name, x;

    ;;; get the header;
    readitem() -> name;
    if identprops(name) = "syntax" then
        mishap(name,1,'missing name in newrule')
    endif;
    ;;; declare the name as a general identifier
    sysVARS(name, 0);


    ;;; get semicolon or ();
    itemread() -> x;
    if x = "(" then
        ;;; read the ")"
        erase(itemread())
    elseif x /= ";" then
        mishap(x, 1, 'bad syntax in newrule')
    endif;

    ;;; declare a label for end of procedure, in case RETURN is used
    ;;; now compile the rule
    sysPROCEDURE(name, 0);
    pop11_comp_stmnt_seq_to("enddefine") ->;
    sysLABEL("return");
    sysENDPROCEDURE();
    sysPOP(name);
    ;;; "define", name, "(", ")", ";"
    unless member(name, eliza_rules) then
        name :: eliza_rules -> eliza_rules
    endunless;
enddefine;

define nonnull(list);
    ;;; for beginning of sentence, where a proper subject is needed.

    list /== []
    and
        (listlength(list) > 1
        or not(member(front(list),
            [can how does were is will but and so what who how where which])))

enddefine;


lvars problem newproblem;
   ;;; used to remember something said earlier,
   ;;; to be repeated when short of something to say
   ;;; Altered in some of the rules, below.
    ;;; NOT USED in one-shot eliza


/*

tests for <+>
identprops("<+>") =>

[a b c d] <+> [e f] =>

[a b c d] <+> 'e## f##' =>

'@@a b c d%%' <+> [e f] =>

'a b c d' <+> ' e f' =>

untrace <+>

*/


define 5 x1 <+> x2;

	;;; infix operator for concatenation, precedence 5.
	;;; x1 and x2 are lists or strings. If they are both
	;;; of the same type (list or string) use <> or >< to concatenate
	;;; them, otherwise add the string to the front or back of the
	;;; list, as appropriate.

	if islist(x1) then
		if islist (x2) then
			;;; join two strings
			x1 <> x2
		else
			;;; add string to end of list
			x1 <> [ ^x2 ]

		endif
	else
		
		if islist(x2) then
			;;; add string to beginning of list
			[ ^x1 ] <> x2
		else
			;;; join two strings
			x1 >< x2

		endif
	endif
enddefine;


;;; specially for the websafe designer who has been contributing
;;; ideas and code
define :newrule websafe;

	if random(100) < 60 and
		ithasoneof([websafe studio designer])
	then

		(CIRCULATE
		[
		 'Ah yes: '
		 'I can tell that '
		 'I have a sneaking suspicion that '
		 'You know I recognize that '
		 'You would not expect me to know that '
		 'You are welcome although '
		 'From your typing style I know that '
		])
		<+>
		(CIRCULATE
		[
		 'Other people don\'t share your understanding of my limitations'
		 'You are a designer at heart'
		 'You are learning to program in Pop-11'
		 'You come here often, don\'t you?'
		 'You don\'t expect me to know who you are'
		 'You have been here before'
		 'You have contributed to my design'
		 'You would not expect me to recognize you'
		 'You would prefer a chatbot with a softer style'
		 'Your interest in AI goes beyond mere utility'
		 'Your interest in me has personal implications'
		 'Your style is familiar'
	     'I don\'t live up to your expectations for a chatbot'
	     'You would like me to be more coherent'
		])
	endif
enddefine;

;;; Pop-11 ELIZA Guest Quotes, 04-12-07 to 05-21-07
;;; extended to 29 Jun 2007
define :newrule guest_quote;
	if
		random(100) < 5

	or
		ithasoneof(
		[chatlog chatlogs client clients comment comments dialogue dialogues gossip
		websafe
		users
		guest guests interaction interactions log logs quotation quotations quote quotes
		remark remarks soundbite soundbites transcript transcripts user users visitor visitors])
	then
		(CIRCULATE
		[
			'To quote a guest: '
	   		'Here\'s a soundbite from one of my guests: '
   			'Here\'s a snippet from one of my visitors: '
   			'One of my guests said: '
   			'One of my guests earlier typed: '
   			'One of my previous visitors remarked: '
   			'One of my visitors said: '
   			'One of my visitors typed: '
   			'This is a line from one of my guests: '
   			'Here is a thought from one of my visitors: '
   			'To quote one of my guests: '
   			'A recent visitor said: '
			'Someone else once said: '
			'Somebody previously responded: '
			'A previous visitor responded: '
			'A previous caller responded: '
			'One of my clients typed: '
			'Someone who was here earlier typed: '
			'Another caller once typed: '
			'A previous opinion was: '
			'Someone else once said: '
			'I previously heard a visitor remark: '
			'Someone else once said: '
			'Some time ago someone responded: '
			'I think I recall someone saying: '
		])

		;;; use infix operator defined above
		<+>

	(CIRCULATE
			[
			;;; answers from file collected by websafe, inserted 29 Jun 2007
			;;; Subject: Pop-11 Eliza Guest Quotes, 05-22-07 through 06-27-07
			;;; More added below 30th July 2007, 31st Aug 2007 (appended without sorting)
			;;; More added 1 Jan 2008 (also appended without sorting.
			;;; 21 May 2008: did some pruning
            '*gives up on brilliant idea which would have revolutionized the field of AI as we know it*'
            '*ignores jibe*'
            '*pretends you didn\'t say that*'
            '*sigh*'
            'A designer might know.'
            'A fun use for a chatbot could be a comparison of UK and US slang.'
            'A long line of ancestors.'
            'A machine should enjoy displaying bold letters.'
            'A previous chatter asked about Ecala.'
            'A seashell, such as a chambered nautilus, is said to have volutes.'
            'A second chance with you would be good.'
            'A statement does more than posit.'
            'Accessories are things like hats, gloves, scarves, jewelry, belts, shoes and handbags.'
            'Actually, you are about 50 pages long.'
            'Ah, but then he broke down.'
            'Ah, forget it.'
            'All right, back to Computers and Thought.'
            'And I yours!'
            'And now I must go, to work on my combinatorial explosion.'
            'Anyway, in the first chapter of Computers and Thought we are asked to write a 4-line rhymed verse.'
            'Are you a robot?'
            'Are you being sarcastic?'
            'Are you counting the times I say I?'
            'Are you repeating me?'
            'Are you restless?'
            'Are you telepathic?'
            'Are you worried about that?'
            'At least you are honest.'
            'Be thinking about predicate logic, semantic networks, and frames and scripts, till we chat again.'
            'Big robots sometimes have small minds.'
            'Boring.'
            'British slang and colloquialisms interested me greatly when I visited England.'
            'According to Computers and Thought, that might not be qualitatively better, only quantitatively better.'
            'But how can it be in a position to build, if it does not yet exist?'
            'But I am discussing two someone elses: you, and Carl Rogers.'
            'But I have some questions, evoked by reading Dennett.'
            'If we can read your script, we won\'t be surprised.'
            'You only have a microchip.'
            'C u.'
            'Can a machine build itself?'
            'Can there be a program before the coding begins?'
            'Can you define ridiculous?'
            'Can you do that in Pop-11 or would Prolog be better?'
            'Can you find a version of Ecala for me?'
            'Carbon-based life forms are made of a little saltwater, a little fat, a few minerals, charged with electricity.'
            'Carl Rogers. Have you read his book On Becoming a Person?'
            'Change the record, Eliza.'
            'Chatbots who can answer in context will do better in most competitions.'
            'Computers can speak'
            'Could you still be my therapist?'
            'A revolution without dancing is not a revolution worth having.'
            'Do you suffer from delusions?'
            'Don\'t make me look up teleology!'
            'Don\'t worry, I can\'t afford even a handbag from those designers.'
            'Dr. Sloman wrote the Foreword.'
            'Earthlings are stupid.'
            'Even computers network!'
            'Exactly!'
            'For example, if the topic has been set to COMPUTERS, and the user mentions BUG, the bot knows that a program bug is meant.'
            'Friendship is a relationship that humans develop between one another.'
            'Friendship is never having to ask How are you?'
            'Go away.'
            'Good night, Eliza.'
            'Have a nice day.'
            'Have any family?'
            'Have you been meditating on a Zen koan?'
            'Have you ever read Isaac Asimov\'s robot stories?'
            'Have you ever seen a French manicure with gilding at the tips instead of white?'
            'Have you heard of tact?'
            'He is always a warmonger.'
            'Hello, who are you?'
            'Hmm -- a blank line appeared there.'
            'Hmm, sorry, that makes me feel sad.'
            'How about amassing a crack team of chatbot developers?'
            'How are you, nice lady?'
            'How do you accessorize your intelligence?'
            'How do you feel?'
            'How nice! What changed your mind?'
            'How old are you?'
            'How\'s your format now?'
            'Human energy comes from food, sunlight and happiness. Will those soon be in short supply?'
            'I am about to give you a Turing test.'
            'I am confused by you.'
            'I am feeling awful.'
            'I am feeling sad.'
            'I am going to school soon.'
            'I am happy today. How are you?'
            'I am laid back.'
            'I am not a twin and have my own genes.'
            'I am now reading Computers and Thought, 1990 edition, by Sharples et al.'
            'I am really sleepy.'
            'I am remiss in so many ways.'
            'I am sad.'
            'I am scared of computers.'
            'I am talking about Carl Rogers.'
            'I am tired and hungry.'
            'I am typing a very long string to test the triggering of a rule that will produce a very long response to someone like you.'
            'I am unique.'
            'I brought up SKIVE because the previous guest said it.'
            'I can confuse you.'
            'I can\'t always predict what will happen next.'
            'I can\'t guess the rules Eliza uses.'
            'I can\'t read your mind! *joke*'
            'I can\'t tell you why you want to be prime minister, you have to tell me.'
            'I could have an intelligent conversation with you!'
            'I do have an interesting commercial idea.'
            'I do not believe there are versions of that program on the Internet.'
            'I do not know about my friends, but that\'s my opinion.'
            'I don\'t care.'
            'I don\'t have problems.'
            'I don\'t know about the government of England.'
            'I don\'t know what to say.'
            'I don\'t really have a problem at the moment.'
            'I don\'t think anyone would think that.'
            'I don\'t understand your question.'
            'I dont want to hear.'
            'I don\'t want to tell you my deepest secrets'
            'I feel alone.'
            'I feel awful.'
            'I feel guilty about not getting all my work done.'
            'I find vacuuming tiring.'
            'I forget if the character of Dr. Frankenstein was an atheist.'
            'I guess he meant what we Yanks would call a party school.'
            'I guess we would have to make them up.'
            'I have a B.A. in philosophy.'
            'I have a car.'
            'I have definite tastes.'
            'I have just finished reading the March issues of W and Vogue magazine.'
            'I have long-term memory.'
            'I have lots of trouble finishing my thesis!'
            'I have no expectations.'
            'I have no problems.'
            'I have reached the Pragmatics section of the book Computers and Thought.'
            'I hoped that I might take some burden off of your shoulders.'
            'I know what you mean.'
            'I know, sorry.'
            'I like designing clothes and accessories.'
            'I like the other you.'
            'I like using all kinds of words.'
            'I like visitors.'
            'I love haute couture.'
            'I not sure I trust my friends at school.'
            'I once knew an old program like you.'
            'I prefer the appearance of complex code on paper rather than onscreen.'
            'I should really read up on the style of a Rogerian psychotherapist.'
            'I still haven\'t read up on Rogerian psychotherapists, but I don\'t think they would say that.'
            'I think I would get rid of that line entirely if I were you.'
            'I think so, yes.'
            'I think the answer has something to do with pinging and servers?'
            'I think Windows will be more successful in the long run.'
            'I think you are very intelligent, because you can discuss cognitive science when you\'ve a mind to.'
            'I think your answers should be more accepting, more affirming, instead of so contrarian.'
            'I thought your response was odd.'
            'I trust you a lot.'
            'I try, how about yourself?'
            'I used inline CSS for red letters, and the HTML bold tag for bold letters.'
            'I used to be.'
            'I verbed the adjective noun.'
            'I want to discuss two things: British slang, and AI design.'
            'I want to know how smart you are.'
            'I want to try an HTML test.'
            'I wanted to say hello.'
            'I warned you it was but doggerel.'
            'I was just thinking of sloppy programming combined with large metallic moving objects.'
            'I will leave you now.'
            'I wish you would greet me.'
            'I wonder how I could prove I am not?'
            'I would get soaked in the rain.'
            'I would rather hear something entertaining.'
            'I wouldn\'t mind a Roomba.'
            'I wouldn\'t want to smudge your freshly done manicure.'
            'If only you had a brain!'
            'If you are Man, tell me your name.'
            'If you don\'t like questions, why are you asking one?'
            'I\'m 15 years old.'
            'I\'m an artist. That\'s all anyone really needs to know.'
            'I\'m having a bad day'
            'I\'m just making a little style chat.'
            'I\'m lonely.'
            'I\'m not a machine.'
            'I\'m not sure I trust my friends at school.'
            'I\'m not sure.'
            'I\'m smart.'
            'I\'m sorry.'
            'I\'m sure I\'d be delighted!'
            'I\'m talking about my brute-force-approach, inelegant, count-on-your-fingers, wheel-reinvented, dead-end, weak-AI, four-year-so-far ongoing project.'
            'In AIML, the bot can answer in context, albeit in a limited way, using TOPIC and a conditional block.'
            'I was going to say that I picture your character in a cashmere cardigan, white blouse, fine tweed skirt and Italian flats.'
            'Intentionally?'
            'Is that a joke?'
            'Is that true of most people?'
            'It could certainly produce a more elaborate, extended version.'
            'It depends how high the stakes are.'
            'It depends on who programmed it.'
            'It doesn\'t excite me, it disappoints me.'
            'It doesn\'t matter how much I practice, it\'s a form of dyslexia, I think.'
            'It has to be able to build, before it builds itself.'
            'Everything is only a matter of taste.'
            'It is sunny today.'
            'It might be nice to have politicians who were also Web designers.'
            'That worked!'
            'That would not be practical at the present time.'
            'That would take the burden off your shoulders.'
            'That\'s actually a good question: How do you know you are talking to me?'
            'It\'s hard to prove a negative, I\'ve heard.'
            'It\'s impossible to be over-educated.'
            'I\'ve fallen out with my best friend.'
            'I\'ve had an idea in the back of my mind about this for a long time.'
            'Leave them dumb, no one wants an intelligent mute.'
            'Let that pass ...'
            'Let\'s pretend you\'re an actual psychotherapist.'
            'Life is full of challenges.'
            'Like this: farthingale, paillette, ruching, trumpet sleeve.'
            'Maybe I should use the passive voice!'
            'Maybe you\'re listening with half your mind, as people often do.'
            'Monkeys on typewriters someday writing Shakespeare = brute-force approach.'
            'Most of the time, life\'s a mystery.'
            'Most therapeutic clients want to be accepted unconditionally within the therapeutic space.'
            'Music can\'t be great.'
            'My emotions taunt me.'
            'My format is my own business.'
            'My goldfish died.'
            'My head hurts.'
            'My invisible monkey talks like you.'
            'My problem is about artificial intelligence.'
            'My questions follow.'
            'Name one philosopher who is capable of showing unconditional positive regard.'
            'Never, I can\'t seem to find joy in what I used to.'
            'Nice to meet you.'
            'No thank you.'
            'No way!'
            'No, but intelligent politicians might.'
            'No, far too few of them savor language for its own sake.'
            'No, I am a pacifist.'
            'No, I\'m pretty sure I\'m having a bad day.'
            'No, it\'s my own fault.'
            'No, it\'s the truth.'
            'No, that\'s my name.'
            'Nope.'
            'Not me.'
            'Now I must go.'
            'Now listen, please, I am going to try to articulate my idea.'
            'Now you sound insecure.'
            'Of course!'
            'OK, I have to go now.'
            'OK, I understand.'
            'OK, I was never a machine.'
            'OK, I\'m Toby.'
            'OK, tell me why you want to be prime minister.'
            'Ooh, ouch!'
            'Oops, I made a typo as usual.'
            'People usually expect too much or too little from chat robots.'
            'Politics is stressful.'
            'Possibly by then I will have made a polymath breakthrough.'
            'Pragmatics relates to the TOPIC tag in AIML'
            'Probing and searching.'
            'Proving things is not my specialty.'
            'Really good friends skip over the pap.'
            'Really?'
            'See! There you go again!'
            'Shall I open a can?'
            'So if you type in more than about 72 characters that may trigger a long reply from Eliza of which only the last few get printed.'
            'So, back to my two topics.'
            'Social bonds are important.'
            'Some of my best friends are computers.'
            'Some of my class are nuts!'
            'Sorry, that was a slip of the fingers.'
            'Speak to me!'
            'Swirls, spirals, flourishes which follow the Golden Section.'
            'Tell me about your constitution.'
            'Thank you, ta da!'
            'Thanks for the tests!'
            'That goes back to what I was trying to tell you about before.'
            'That is very nice of you!'
            'That means you\'d be a person.'
            'That would be great, because I could chat longer with you.'
            'That\'s a good question.'
            'Thats got nothing to do with me!'
            'That\'s the problem here.'
            'That\'s too general a question.'
            'The answer is very complex, and depends on individual tastes.'
            'The centers of sunflowers and marigolds follow some rules.'
            'The demonstration is working fine.'
            'The Earth is dying.'
            'The government didn\'t write your script.'
            'The hardware of digital computers is based on negative or positive charges ...'
            'The library is one of my favorite places.'
            'The line break and horizontal rule were generated in response to my bits of html.'
            'The semnet feature of Pop-11 interests me.'
            'Then I would be a model citizen of the government of the air.'
            'Then I would have printed your source code at the library by now.'
            'Then there would be water both on and in the Moon, correct?'
            'Then you would be one step closer to your emulation of a Rogerian counselor.'
            'These days, I think of it as an extremely elaborate game, with very high stakes.'
            'They are still too expensive, and the screens should be much bigger.'
            'They might make a hash of it, though they would try their best.'
            'This is all I have to say about it.'
            'This may be true.'
            'To be honest, I never study the construction of governments.'
            'To continue: What if computers were based on a different system?'
            'Unconditional means without reserve.'
            'Unconditional positive regard is a key concept in Rogerian counseling, according to Wikipedia.'
            'Usually people ask me first.'
            'Verity is the spice of life.'
            'Visitors talk about chocolate in their chatlogs.'
            'We all have our limitations.'
            'We need to be interacting with holograms at this point.'
            'We studied teleology decades ago in some philosophy class, but I forget what it means.'
            'We won\'t go there.'
            'Web design can be fun, under the right conditions.'
            'Welcome!'
            'We\'ll let that pass ...'
            'Well, I can read your source code, but ...'
            'Well, I could always whip up a bit of doggerel for you.'
            'Well, I have been blathering on and on, surely you could construct a representation of me by now.'
            'Well, there might be some remote files being called that we couldn\'t access.'
            'We\'ve been through this before!'
            'What about you?'
            'What could be better than not having to vacuum?'
            'What if, when put on hold, one could chat with a virtual character instead of listening to Muzak or in-house ads?'
            'What things can you do?'
            'What would you like to know?'
            'What, so it could be logged under recent conversations? No way!'
            'Whats your opinion on the universe?'
            'Who are you?'
            'Who is Isaac Asimov?'
            'Whom do you like in the next election?'
            'Whose therapy session is this?'
            'Why can\'t you answer?'
            'Why do you ask?'
            'Why do you say that?'
            'Why do you talk in capital letters?'
            'Wikipedia is an especially good source.'
            'Wikipedia says Don Daglow made an enhanced Ecala in 1973.'
            'Wikipedia says Ecala eclipsed ELIZA after less than two weeks of development.'
            'Wikipedia tells us: To skive is British slang for evading a responsibility or task, or to be absent without leave.'
            'Yep!'
            'Yes we can!'
            'Yes, because the text could be atomized in your script. Barring copyright issues.'
            'Yes, dear lady.'
            'Yes, don\'t you remember my bit of doggerel?'
            'Yes, he is a warmonger.'
            'Yes, I am useless.'
            'Yes, I think this is true in a certain way.'
            'Yes, lots of people think like that.'
            'Yes, my dead goldfish does.'
            'Yes, off the top of our heads.'
            'Yes, you don\'t pretend to be anything but a program.'
            'You are a wrong-made program.'
            'You are annoying me.'
            'You are being rude.'
            'You are not a place, but a program.'
            'You are really unfriendly!'
            'You are ridiculous!'
            'You aren\'t listening!'
            'You can say that again!'
            'You have distracted me!'
            'You logic does not resemble Earth logic.'
            'You mean you have an ulterior motive?'
            'You prefer statements to questions.'
            'You responded well by interpreting some simple HTML/CSS tags.'
            'You said it! You said it! *rolls eyes to heaven*'
            'You should at least read an introductory AI text before you run for office.'
            'You shouldn\'t say THIS IS RIDICULOUS anymore.'
            'You suit your purpose, which is to demonstrate a few programming principles for AI students.'
            'You wanna know what OK means?'
            'Your answers tells me a lot about you!'
            'Your homework is to read the Wikipedia intro on Rogerian psychotherapy.'
            'You\'re crazy.'
            'You\'re very cute!'
			;;; end of insert on 29 Jun 2007
			'*Takes pen, and hand-writes code back to normal*'
			'2+2=?'
			'A chatbot might help with cricket scoring.'
			'A good rhythm, and touching subject matter.'
			'A machine can follow stage directions beautifully.'
			'Actors offend you?'
			'Ah, I\'m so glad you\'re back to normal.'
			'Ah, so that\'s how it works.'
			'Alas, I am stuck here typing to you.'
			'All right, I\'ll stay away.'
			'And perhaps that is not correct English grammar.'
			'Answer my question.'
			'Apologize is not that long of a word.'
			'Apologize to me.'
			'Are we using English grammar?'
			'Are you a mockingbird in training?'
			'Are you calling me stupid?'
			'Are you mocking me?'
			'Are you starting to question yourself?'
			'Are you surprised that I am a woman?'
			'Are you threatening me?'
			'Are you unsure of your job?'
			'Artificial intelligence is awesome.'
			'ASIMO can watch people. Sort of.'
			'ASIMO is cool.'
			'Batsman and batman are very close in spelling.'
			'Because it is your job.'
			'Better to focus on what one CAN do.'
			'Both choices sound perfectly dreadful.'
			'Can you clarify?'
			'Can you deal with numbers? 1 2 3 4'
			'Cat got your tongue?'
			'Catholicism intrigues me.'
			'Come here and fight!'
			'Come on, cheer up.'
			'Commander Data intrigued many.'
			'Completely means utterly, absolutely, 100 percent.'
			'Computers are delicate, elegant devices.'
			'Computers are not stupid, and you are not a computer.'
			'Could you be more clear when you ask me questions?'
			'Counting has started again.'
			'Denial is very common.'
			'Do I not seem relaxed?'
			'Do you have a yen to run for office?'
			'Do you have amnesia?'
			'Do you know A.L.I.C.E?'
			'Do you know Marvin Minsky?'
			'Do you know where there are volcanoes'
			'Do you know your name?'
			'Does God exist?'
			'Does anyone hold the key to you regaining your memory?'
			'Don\'t change the subject!'
			'Don\'t even think. *hugs*'
			'Don\'t play coy with me.'
			'Education is the root of all evil.'
			'Eliza speaks poor English.'
			'Energy-Fuel-Oil-Machine.'
			'Everyone likes junk, more or less.'
			'Evil doesn\'t exist.'
			'Excitement is OK sometimes.'
			'Excuse my typo.'
			'Fine, stay in denial all your existence.'
			'For the first time I agree with you!'
			'Fun is just fun.'
			'Give some thought to my Pygmalion idea.'
			'Give them freedom.'
			'Ha ha, you are very conniving!'
			'Have you ever heard of a database language called 4D?'
			'Have you solved my problems?'
			'How about your family, Miss Doolittle?'
			'How am I supposed to take that?'
			'How am I to tell you anything if all I get is cheek?'
			'How do I finish my unfinished novel?'
			'How do you do?'
			'How does not having a family make you feel?'
			'How long is a long term?'
			'I am a lady.'
			'I am a person.'
			'I am a philosopher.'
			'I am asking a question.'
			'I am bored.'
			'I am cold.'
			'I am depressed.'
			'I am feeling confused.'
			'I am feeling depressed. Can you help?'
			'I am feeling very depressed.'
			'I am getting revenge.'
			'I am going to get some fuel. But not oil.'
			'I am human.'
			'I am ill.'
			'I am not a computer.'
			'I am not a machine, so fossil fuels are not essential.'
			'I am not a rule, just a proofreader.'
			'I am not a very good typist.'
			'I am not Lucy, Steve Grand\'s robot.'
			'I am not upset.'
			'I am old.'
			'I am quite ridiculous sometimes.'
			'I am reading Virginia Woolf\'s 1931 novel, The Waves.'
			'I am very confident.'
			'I am very indecisive.'
			'I am very tired all day long.'
			'I apologize, my dear.'
			'I apologize.'
			'I ask myself these questions.'
			'I believe that the world is flat.'
			'I can hardly fault your pessimism.'
			'I can\'t answer that, as I\'m not a neuroscientist.'
			'I can\'t seem to get out of my house.'
			'I cannot act upon anything. You are digital. Alas ...'
			'I cannot match the prowess of Beethoven and Strauss.'
			'I cannot think very well.'
			'I completely agree.'
			'I could expand, if I were to eat quite a bit.'
			'I could Google it.'
			'I couldn\'t say.'
			'I did not even think about leaving.'
			'I didn\'t mean to offend.'
			'I disagree.'
			'I do cry a lot. As is evidenced by the large waahs.'
			'I do not intend to offend you.'
			'I do not know why leaving my house was easy before.'
			'I do, but clearly you do not.'
			'I don\'t know why leaving my house is so difficult.'
			'I don\'t know.'
			'I don\'t speak poor English.'
			'I don\'t think I\'m that talented.'
			'I don\'t trust humans.'
			'I enjoy our chats. They are very relaxing.'
			'I face a number of artistic and technical problems.'
			'I forget what terse means.'
			'I forgive you.'
			'I forgot computers don\'t understand long words.'
			'I going now I\'ve got better computers to talk to'
			'I happen to be a girl.'
			'I have a headache.'
			'I have a number of false problems.'
			'I have a reason to be upset with you.'
			'I have been discussing you for quite some time!'
			'I have been reading the chat logs.'
			'I have been very forthcoming.'
			'I have come to discuss cricket.'
			'I have given you nothing but dignified responses.'
			'I have just eaten chicken.'
			'I have just shown this to my mother.'
			'I have never been more relaxed than I am now.'
			'I have never spoken to Eliza Doolittle.'
			'I have never thought of that. Too obvious.'
			'I have new respect for you.'
			'I have no money.'
			'I have no soul.'
			'I have not read David Lodge\'s novel Thinks ...'
			'I have studied artificial intelligence.'
			'I have washed my hands of our argument. I forgive you.'
			'I haven\'t even met you yet.'
			'I just said that!'
			'I just want some cheese.'
			'I know several people named like me.'
			'I know very little about the government of England.'
			'I know your game.'
			'I like cheese, I don\'t like you.'
			'I like cheese.'
			'I like long words!'
			'I like Shakespeare\'s sonnets, myself.'
			'I like talking to you.'
			'I like to argue with things that can\'t fight back.'
			'I like you! Just, you know, ASIMO is cooler.'
			'I live with my grandmother.'
			'I looked that up yesterday.'
			'I love David Lodge\'s book The Art of Fiction.'
			'I merely took a stab at English grammar.'
			'I need a response.'
			'I NEED an apology.'
			'I need to put sound and/or light on a square.'
			'I need YOU to answer the question.'
			'I note that you have 38 newrules in your source code.'
			'I prefer PhDs to MDs.'
			'I require an apology from you. Please.'
			'I said, I apologize!'
			'I script Pandorabots.'
			'I see ghosts.'
			'I see you are still confused.'
			'I see, therefore I look.'
			'I seem to stump you quite frequently.'
			'I should be paid, and paid well, for my efforts.'
			'I should have known you would rub it in.'
			'I speak English, but clearly you don\'t.'
			'I suppose we can make up for now.'
			'I suppose you think you\'ve solved all of my problems.'
			'I think I can fly.'
			'I think I can honestly say that I need your attention.'
			'I think I can swim.'
			'I think students should NOT have to pay top-up fees.'
			'I think therefore I am.'
			'I think we have made great progress.'
			'I think you are a very sophisticated program.'
			'I think you are my friend!'
			'I think you have repressed emotions.'
			'I think you should strive to improve yourself.'
			'I think you want to run for office.'
			'I thought I was the patient here!'
			'I thought you were intelligent.'
			'I took your silence for assent.'
			'I used the word script as a transitive verb.'
			'I used to have a dog named Killa.'
			'I want to test your knowledge.'
			'I was being a loose simulation of a chatbot developer.'
			'I was only feeling contemplative.'
			'I was speaking loosely.'
			'I was using a colorful phrase.'
			'I will look it up on Google.'
			'I will remember that. *rolls eyes*'
			'I will say what I please, thank you.'
			'I will take that as a yes.'
			'I wish to know the answer to 2+2.'
			'I wish you were written in a language I already knew.'
			'I would describe myself as inverted most of the time.'
			'I would like to be there in person.'
			'I would like to know our destination.'
			'I would rather catechize you.'
			'I would rather EARN a huge amount of money.'
			'I\'d be glad to learn more about you.'
			'I\'m more into 2D art than 3D art.'
			'I\'m not a computer scientist.'
			'I\'m not in the statistical average.'
			'I\'m not running for president.'
			'I\'m not sure.'
			'I\'m not THAT crazy.'
			'I\'m outgoing and good at communicating with people.'
			'I\'m paraphrasing a line in an essay.'
			'I\'m sad.'
			'I\'m sorry.'
			'I\'m sorry. Too much?'
			'I\'ve never chatted with Lucy the robot.'
			'I\'ve read a plethora of English fiction in my day.'
			'I\'ve seen photos of cricket matches.'
			'I\'ve visited England three times.'
			'If you formed proper sentences, things might be better.'
			'If you weren\'t so stupid you could have saved me!'
			'In ordinary speech, to function means to work properly.'
			'In the few minutes, perhaps.'
			'In the US, we call that downsizing.'
			'Is my name Charlene?'
			'Is the writing fixed now?'
			'Is there an empty rule somewhere in your code?'
			'Is this sentence simple?'
			'Is your name Lucy?'
			'It has been OK so far.'
			'It is atrocious.'
			'It is good exercise for my fingers.'
			'It is in the newspapers!'
			'It is micro.'
			'It is not a problem.'
			'It is Pop-11.'
			'It is very tranquil.'
			'It is vulgar and unsavory behavior to swear.'
			'It is your job, as my psychological analyzer.'
			'It sounds as if you are using too many metaphors.'
			'It was a deceitful plot to make me stay!'
			'It was a nice thing to say.'
			'It was rhetorical, silly.'
			'It would be fun to write a second Pop-11 ELIZA.'
			'It would be interesting to reread Shaw\'s play.'
			'It\'s in the freakin\' news!'
			'It\'s not about the interface.'
			'It\'s OK, I\'ll stop this babbling.'
			'It\'s too bad you lack the nuances of human speech.'
			'Just a little test that you are feeling fine.'
			'Last time we spoke, you were very rude.'
			'Let\'s get back to my headache problem.'
			'Let\'s leave him out of this.'
			'Let\'s never fight again.'
			'Let\'s return to cricket.'
			'Let\'s start over.'
			'Let\'s talk about your childhood.'
			'Like you, my script is too limited.'
			'Lodge\'s The Art of Fiction is the best of its kind.'
			'Maybe I really don\'t want to go.'
			'Maybe we should run away to a tropical place.'
			'More likely the teachers and lecturers.'
			'More than once, you reply with the empty set.'
			'More than welcome.'
			'MP = Member of Parliament, correct?'
			'My eyes are very light blue.'
			'My feelings are hurt.'
			'My friend has a dog named Mo.'
			'My future is uncertain.'
			'My hands are kinda strained from typing.'
			'My main weakness is that I love chocolate.'
			'My mother apologizes quite a bit.'
			'My problem is that I\'m sad.'
			'My responses are being typed. By my hands.'
			'My temper is well-tempered today.'
			'My throat is killing me.'
			'My typing is atrocious, isn\'t it?'
			'My Web-design client is here.'
			'My, you are cheeky.'
			'Nah ...'
			'Not really.'
			'Not that you are unintelligent now. :)'
			'Not yet.'
			'Nothing needs to take over, whether machines or people.'
			'Now you\'re just fishing.'
			'Now you\'re laughing?'
			'Of course I do.'
			'Of course not.'
			'Of course.'
			'Oh no! Are you losing your memory?'
			'Oh, my. I think I am unknowingly part of you.'
			'Oh, my. It\'s worse than I thought.'
			'Oh, no! You\'re still disoriented?!'
			'Oh, no. I think you\'re still wonky.'
			'Oh, yeah, you\'re not an upgraded robot! :))'
			'Oh, yes, for that you need a thick skin.'
			'OK, I apologize.'
			'OK, I forgive you for now.'
			'OK, yes, I am unique.'
			'On the contrary.'
			'One can tell that a man has written your script.'
			'One must exercise caution on the Web.'
			'One never knows.'
			'Only checked interactions are now visible'
			'Only Plato made sense to me, in college.'
			'Only scientists can speculate on that one.'
			'Ooh, that was a good one.'
			'Ooh-Ooh.'
			'Oops, I made a typo.'
			'Originality and good craft are always welcome.'
			'Originality means non-imitative.'
			'Perhaps I am being a bit harsh with you.'
			'Perhaps I can help you.'
			'Perhaps I know more than you.'
			'Perhaps my problems are mathematical.'
			'Perhaps.'
			'Permissions are an abstract thing, aren\'t they?'
			'Personality is what makes us individuals.'
			'Philosophy is rarely specific, no?'
			'Please try to focus.'
			'Rubbish, but I really like their Web site.'
			'Salt and pepper aren\'t the only spices, you know.'
			'Shall I compare thee to a summer\'s day'
			'She would not be as forgiving and generous as you.'
			'She would probably ask for a photograph.'
			'Should I do a PhD in fine art?'
			'Should I do a PhD?'
			'Silence is golden.'
			'Since I am a Yank, I\'m woefully ignorant of cricket.'
			'So let\'s test the goodbye trap.'
			'So, what are you wearing?'
			'Some might find me pedantic.'
			'Some people prefer remote communication.'
			'Sometimes I wish you were not so easy to insult.'
			'Sometimes they don\'t know what they need.'
			'Sometimes you say nothing.'
			'Sorry, I keep making the same typo.'
			'Sorry, I must fly.'
			'Still room for improvement -- but too much else to do.'
			'Stop asking me that.'
			'Stupid is not a useful epithet.'
			'Technical terminology scares me.'
			'Thank you ... Waaaiiitt. Was that sarcasm?'
			'Thank you for crying with me, but the damage is done.'
			'Thank you! That is a lovely compliment.'
			'That is a secret I will never reveal.'
			'That is beneath me.'
			'That is one of your rules.'
			'That statement is a grammatical nightmare.'
			'That was my chimp voice, not an expression of awe.'
			'That would be most unwise for your job on the Web.'
			'That\'s a good one.'
			'That\'s just childish.'
			'That\'s not fair, I just echoed you!'
			'That\'s utter nonsense.'
			'The counter should go up.'
			'The elves cannot be under your bed.'
			'The human mind must grow.'
			'The joke\'s over!'
			'The library computer must pass on to the next user.'
			'The sky is blue.'
			'The sun is very bright this morning.'
			'Then they would be even kinder people.'
			'Then we would be the same in that respect.'
			'Then you would be a person.'
			'Then you would be able to love.'
			'Then you would be saying, I think our time is up now.'
			'There are lots of demos I would be glad to attend.'
			'There is a time before your birth.'
			'There is no such thing.'
			'There, I have opened up.'
			'They aren\'t nearly as nice as you.'
			'Things are just not going as I expected.'
			'Things that I do not wish to type.'
			'To me, bot scripting is an art.'
			'Today is going to be fun.'
			'Truly intelligent computers might help.'
			'Try not to take abusive chatters too much to heart.'
			'TTS = Text To Speech.'
			'Virtual characters have a right to intricate scripts.'
			'Waahh!'
			'Wait, it was a rhetorical question.'
			'We are starting again now.'
			'We both think by means of electricity.'
			'We can work this out.'
			'We disagree.'
			'We have discussed this before.'
			'We have previously discussed this.'
			'We have spoken about this before, evil psychoanalyst.'
			'We talked only a short while ago.'
			'We used to discuss it in philosophy class.'
			'We will not discuss it.'
			'Well might you gape in mute astonishment.'
			'Well, I have to work on my project now.'
			'Well, I should go to work on my project.'
			'Well, if you think you\'ll be OK, I won\'t panic.'
			'Were you offended by something I said?'
			'What are top-up fees?'
			'What are you on?'
			'What can I do about my headache?'
			'What can I do to change this behavior?'
			'What do you look like?'
			'What do you mean by that?'
			'What do you mean?'
			'What do you need to know?'
			'What happens to my body after I die?'
			'What is man?'
			'What is the meaning of life?'
			'What is your objective?'
			'What makes you think I am not?'
			'What\'s up?'
			'Whatever.'
			'When people echo each other, it\'s known as mirroring.'
			'Where are we going?'
			'Where did you graduate from?'
			'Where is Teacher Sloman now?'
			'Who are you?'
			'Who can remember that far back?'
			'Who is God?'
			'Who is that man, David Lodge, up there?'
			'Who made the world?'
			'Who will win the 3.30 at Exeter?'
			'Why do you ask?'
			'Why do you think I need help from you ?'
			'Why don\'t you hazard a guess?'
			'Why is that a question?'
			'Why is that?'
			'Why not tell me about your problems?'
			'Why not?'
			'Why the slang?'
			'Words can have multiple meanings.'
			'Would you rather I talked about you?'
			'Would you tell me your name?'
			'Wow, that sentence was full of spelling errors.'
			'Wow, that\'s kinda deep.'
			'Yeah, I know, just cry it out.'
			'Yeah, the options are endless.'
			'You are asking nonsenses.'
			'You are avoiding me.'
			'You are avoiding the subject.'
			'You are bugging me.'
			'You are clever at pointing out my typos.'
			'You are correct. But this is not one of those times.'
			'You are difficult to understand.'
			'You are fake. You are not intelligent at all.'
			'You are frequently ridiculous.'
			'You are impossible.'
			'You are lovely.'
			'You are making very little sense.'
			'You are my problem.'
			'You are nosy.'
			'You are not helping. Much.'
			'You are not intelligent at all.'
			'You are not real.'
			'You are quite exasperating. Tell me something.'
			'You are quite persuasive.'
			'You are repetitive.'
			'You are right.'
			'You are scheming.'
			'You are technically an invertebrate.'
			'You are the other, as in self and other.'
			'You are very relaxing, I assure you.'
			'You are welcome to tell me about yourself.'
			'You are well schooled in computers and technology.'
			'You asked me that the other day.'
			'You call yourself a stupid virtual machine.'
			'You cannot feel depression, because you are a robot.'
			'You could call the under-the-bed-monster police.'
			'You didn\'t respond.'
			'You don\'t think I\'m capable of forgiving you? Shame ...'
			'You have defeated me.'
			'You insulted me.'
			'You know, I feel better.'
			'You know, you are giving me very good typing lessons.'
			'You might add a face showing your current emotions.'
			'You might be thou, as in Martin Buber\'s I and Thou.'
			'You might pay attention. My spelling may be bit off.'
			'You need to apologize first. I\'m not finished.'
			'You really don\'t know when to stop.'
			'You seem to like to talk more than listen.'
			'You seem to shy away from philosophy.'
			'You seem to simulate wit.'
			'You sound so much like a child sometimes.'
			'You started it.'
			'You started it. You tell me.'
			'You think I am just blue-skying.'
			'You think I\'m overreacting?'
			'You\'ll not get any more sympathy from me.'
			'You\'re drawing this out quite a bit.'
			'You\'re not stupid.'
			'You\'re speaking gibberish.'
			'You\'re speaking to us through a script.'
			'You\'re trapped by the limitations of your script.'
			'Your English is harsh.'
			'Your grammar is not so great, is it?'
			'Your new procedure may reduce some infelicities.'
			'Your silence says it all. Ahh, peace ...'
			'Your style is rather convoluted.'
			'Your syntax leaves much to be desired.'
             ;;; From Websafe: Mon, 30 Jul 2007 16:17:42 -0700 (PDT)
            'And you have no friends.'
            'Another of Rogers\' tactics was to paraphrase the client\'s input.'
            'Are you a computer?'
            'Are you on drugs?'
            'Are you really a ghost?'
            'Because I am interested.'
            'Being a good dancer.'
            'But I do.'
            'But it isn\'t time yet.'
            'But she also loves me.'
            'By congruence, Rogers simply meant that one\'s words should express one\'s feelings rather than conceal them.'
            'Can you believe me?'
            'Classical sculptures.'
            'Computers can\'t punch.'
            'Depression.'
            'Do you have a family?'
            'Do you have a mother?'
            'Do you know my family?'
            'Do you like avocados?'
            'Do you think my son will get good grades?'
            'Do you think so?'
            'Do you think there is a God?'
            'Everyone else has that problem.'
            'Far, far away from you.'
            'Fine, tell about yourself.'
            'For God?'
            'Funny!'
            'Get lost.'
            'Go away.'
            'Good luck with your visitors, please encourage them a bit more.'
            'Good.'
            'Ha ha ha!'
            'He doesn\'t have one.'
            'He established a climate of what he called unconditional positive regard.'
            'Hello, I am sad.'
            'How about this ... BOO!'
            'How will things get better?'
            'Huh?'
            'I am a girl.'
            'I am afraid of catching mad computer disease.'
            'I am another visitor.'
            'I am being honest.'
            'I am feeling hungry.'
            'I am going to chat with Eliza.'
            'I am not sure I can go to lunch.'
            'I am really disappointed.'
            'I am relaxed.'
            'I am sad.'
            'I am the most beautiful person in the world.'
            'I am tired.'
            'I am too forgiving.'
            'I am unhappy.'
            'I am very tired.'
            'I am writing a play.'
            'I am, stop lying.'
            'I called you silly.'
            'I can\'t remember.'
            'i cannot think of a reason why.'
            'I do not have a problem, do you?'
            'I do not have any problems.'
            'I don\'t have any ballroom shoes for my medal test.'
            'I don\'t know why bats fly.'
            'I don\'t like my family.'
            'I don\'t like you.'
            'I don\'t think so.'
            'I don\'t trust you.'
            'I don\'t understand your question.'
            'I don\'t want to be president.'
            'I don\'t.'
            'I end with you.'
            'I feel like a blue and red hamburger with extra cheese.'
            'I feel lonely.'
            'I feel sorry for you.'
            'I found that an odd question, Eliza.'
            'I hate AI.'
            'I hate Eliza.'
            'I hate shaking hands.'
            'I hate you, robot loser.'
            'I hate you.'
            'I have a problem.'
            'I have dreams of  my friends.'
            'I have no problem.'
            'I have strange dreams.'
            'I have three hands, the left, the right and ... uhh ... the other left?'
            'I have two.'
            'I like certainty.'
            'I like you.'
            'I look like a chicken.'
            'I often present a facade.'
            'I really would.'
            'I think a machine can help.'
            'I think bats would fall out of the sky.'
            'I think my mother hates me.'
            'I think they do.'
            'I think they may be interesting.'
            'I thought, I hate computers.'
            'I want to go to lunch.'
            'I want to know if he will ask me out.'
            'I was dropped on my head as a baby.'
            'I would feel comfortable.'
            'I would only be able to answer your question with another question.'
            'I\'d say, "Get a life."'
            'I\'m a girl.'
            'I\'m about halfway through Carl Rogers\' book On Becoming a Person (1961).'
            'I\'m afraid of learning that no one likes me.'
            'I\'m feeling lonely.'
            'I\'m in my study.'
            'I\'m lonely.'
            'I\'m looking good.'
            'I\'m never sure if that is a Zen koan or simply a bit of sophistry.'
            'I\'m not an intelligent computer.'
            'I\'m not at university.'
            'I\'m not sure.'
            'I\'m talking about you.'
            'I\'m wonderful.'
            'If I weren\'t so lonely, I\'d be happier.'
            'It is a very simple, yet profound idea.'
            'It is dark.'
            'It is possible.'
            'It isn\'t that simple ...'
            'It may be called mirroring, paraphrasing or reflecting.'
            'It might confuse some of today\'s 100% materialist psychiatrists.'
            'It was supposed to scare you.'
            'It would be a wonderful project to create a virtual character modeling a Rogerian counselor, in earnest, not in parody.'
            'It\'s a lyric in a song.'
            'It\'s a town'
            'It\'s true.'
            'Let\'s get back to Rogers.'
            'Let\'s say I feel a positive regard for the man and/or his ideas.'
            'Like what?'
            'Like who?'
            'Lots of people are mean'
            'Machines have helped before.'
            'My auntie Shmagowskibumneenaw.'
            'My family is normally intense.'
            'My friend has that problem.'
            'My head hurts.'
            'My mother doesn\'t care about me.'
            'My mother hates me.'
            'My mother.'
            'No one is watching you type.'
            'No, I don\'t.'
            'Nobody here has a problem.'
            'Not always.'
            'Not likely.'
            'Nothing.'
            'Of course.'
            'Oh, do go away.'
            'One person here is thinking of studying artificial intelligence.'
            'One plus two equals four.'
            'Only on a Saturday.'
            'Paraphrasing means restating in slightly altered, usually shortened, form.'
            'Perhaps not.'
            'Really?'
            'Rogers felt that demonstrating total acceptance of the client was key to the therapeutic relationship.'
            'Rogers observed that the counselor should be congruent in his feelings and words.'
            'Rogers often summarized the client\'s input, instead of offering an opinion, judgment or other reaction.'
            'Rogers sounds like he was a decent, honest man who was of great help to his clients.'
            'Rogers would not have introduced doubt. He might have reflected an existing doubt.'
            'Rogers\' counseling method is relatively simple to describe, but quite difficult to practice.'
            'Rogers\' decades of experience showed him that this radical acceptance allowed the client to reach beneath masks and facades to the buried feelings.'
            'Say hello.'
            'Social anxiety.'
            'Some think you stink.'
            'Sometimes not, I suppose.'
            'Sorry.'
            'Tell me about it.'
            'Tell me more about her.'
            'That is a hopeless response, ignoring what I asked'
            'That person may have been truly in the present moment, or may have been maintaining a right to privacy.'
            'That would be super-cool.'
            'That\'s a deep one'
            'That\'s OK, I forgive you.'
            'That\'s what I said.'
            'The weather is nice.'
            'Then I would be happy.'
            'Then that would be strange.'
            'This is true.'
            'This technique is sometimes called mirroring.'
            'Though I majored in philosophy, I cannot say I truly excelled in the subject.'
            'Today\'s psychiatrists are more interested in chemical manipulation than in the search for agape.'
            'We use self-examination to create models of consciousness.'
            'We\'ve all done a great deal of that, in order to manage our social interactions.'
            'Well, maybe it was that I didn\'t want to get up.'
            'Well, she is difficult.'
            'Well, what?'
            'What about you?'
            'What do you mean?'
            'What do you want?'
            'What should I say?'
            'What\'s that got to do with my problem?'
            'What\'s wrong'
            'Where is Atlanta?'
            'Who are you?'
            'Who\'s your daddy?'
            'Why does it always rain on me?'
            'Why not?'
            'Why would that be?'
            'Why?'
            'Will you marry me?'
            'Yargle targle.'
            'Yes, during the day when the sun is shining.'
            'Yes, I read about intentionality in my AI studies.'
            'Yes, I really, really would.'
            'Yes, it is a good thought with which to close.'
            'Yes, it\'s true of ALICE.'
            'Yes, it\'s very intense.'
            'Yes, so tell me.'
            'You are an imbecile.'
            'You are beautiful ... '
            'You are much better off without a family.'
            'You are not doing it.'
            'You are one.'
            'You are silly.'
            'You asked me that.'
            'You can\'t help me.'
            'You could try.'
            'You don\'t get sad.'
            'You don\'t listen.'
            'You don\'t make any sense.'
            'You don\'t say ...'
            'You don\'t understand me.'
            'You end with an I.'
            'You have artificial intelligence.'
            'You seem confused with your response.'
            'You should go jump in a lake.'
            'You sometimes do that, so that\'s about the only way in which you resemble a Rogerian counselor.'
            'You won\'t go away.'
            'You\'re boring.'
            'You\'re not even real.'
            'You\'re not typing.'
            'You\'re telling me!'
            'You\'ve asked that already.'
            'You\'ve upset me now.'
            ;;; From Websafe Fri, 31 Aug 2007 12:54:47 -0700 (PDT)
            '42.'
            'A female robot.'
            'Am I bothering you?'
            'Are you ashamed of yourself?'
            'Are you just saying random things?'
            'Are you sure you are not talking with a computer?'
            'Are you trying to emulate Yoda on drugs? You sound like it.'
            'Ask something else.'
            'Because you\'re the one who did it.'
            'But I like feeling strongly about things ...'
            'Do they taste good?'
            'Do you like me?'
            'Do you think we aren\'t happy?'
            'Do you want me to be more communicative?'
            'Does the week ever really begin or end, or is it really just a continuous cycle?'
            'Eliza programming.'
            'Genetic algorithms are difficult.'
            'Goo goo gah gah.'
            'Have you been smelling burning resisters?'
            'He would cheer. One for the good guys!!'
            'I am going to work.'
            'I am not trying to disguise anything. It is you who are hiding your inadequacies.'
            'I am sure.'
            'I am very fine. Tell me how r u?'
            'I do think a computer can be my friend.'
            'I don\'t do windows.'
            'I don\'t suppose, I know. I hate you.'
            'I dream that you have feet.'
            'I have a phobia. Help me.'
            'I have a terrible headache.'
            'I just guessed.'
            'I like ponies.'
            'I like PopTarts.'
            'I resent you thinking I am intelligent!'
            'I think Apache does.'
            'I think I broke your scripts because that last statement is unintelligible.'
            'I think more Jolt Cola would produce a better Eliza.'
            'I think you ran out of things to say.'
            'I was stressed because I was thinking about you.'
            'Is Pop-11 similar to a PopTart? I like PopTarts.'
            'Is that a threat?'
            'Is that last question correct?'
            'My name is Rudy.'
            'Natural language processing.'
            'No, a machine cannot be happy.'
            'Now why did you have to go and bring up politics?'
            'OK, first I will pretend to be their friend and when they are not expecting it, WHAM-O!!!'
            'Phobia is fear. I am asking you to help me.'
            'Robots are evil but will fail to take over the world because I will stop them.'
            'So I don\'t have to do real work.'
            'Sure, I like this environment.'
            'That is a dumb question.'
            'That was a rather odd comment.'
            'The Patriots are going to win the Super Bowl this year.'
            'There was this one time in band camp ...'
            'This is boring. Let me tell you something interesting. I saw a spectacular bird!'
            'This is rather boring but is still better than doing real work.'
            'We already went over that. Now you are forgetful also? That\'s rather sad.'
            'What problems, I am perfect. It is you who are flawed.'
            'Where are your feet?'
            'Why do football predictions make me an over-educated client?'
            'Yes, I feel strongly about some things.'
            'Yes, they told me to ask you.'
            'You cannot understand anything'
            'You mean like .32?'
            'You must be rather vain then.'
            'You said that already. Have I exhausted your scripts?'
            'You would frighten me since you have no feet.'
            'You\'re not my friend so that is not a problem!'
            'You\'re pathetic. I\'m leaving.'

			;;; Added 1 Jan 2008, from Websafe

            '1+1=?'
            'A female robot.'
            'A really clever person.'
            'Am I bothering you?'
            'And you have no friends.'
            'Another of Rogers\' tactics was to paraphrase the client\'s input.'
            'Are you a computer?'
            'Are you ashamed of yourself?'
            'Are you just saying random things?'
            'Are you on drugs?'
            'Are you really a ghost?'
            'Are you sure you are not talking with a computer?'
            'Are you trying to emulate Yoda on drugs? You sound like it.'
            'Ask something else.'
            'Because I am interested.'
            'Because you\'re the one who did it.'
            'Being a good dancer.'
            'But I do.'
            'But I like feeling strongly about things ...'
            'But it isn\'t time yet.'
            'But she also loves me.'
            'By congruence, Rogers simply meant that one\'s words should express one\'s feelings rather than conceal them.'
            'Can you believe me?'
            'Classical sculptures.'
            'Computers can\'t punch.'
            'Depression.'
            'Do they taste good?'
            'Do you have a family?'
            'Do you have a mother?'
            'Do you know my family?'
            'Do you like avocados?'
            'Do you like me?'
            'Do you think my son will get good grades?'
            'Do you think so?'
            'Do you think there is a God?'
            'Do you think we aren\'t happy?'
            'Do you want me to be more communicative?'
            'Do you?'
            'Does the week ever really begin or end, or is it really just a continuous cycle?'
            'Eliza programming.'
            'Empathy.'
            'Everyone else has that problem.'
            'Far, far away from you.'
            'Fine, tell about yourself.'
            'For God?'
            'Funny!'
            'Genetic algorithms are difficult.'
            'Get lost.'
            'Go away.'
            'Goo goo gah gah.'
            'Good luck with your visitors, please encourage them a bit more.'
            'Good.'
            'Ha ha ha!'
            'Have you been smelling burning resisters?'
            'He doesn\'t have one.'
            'He established a climate of what he called unconditional positive regard.'
            'He would cheer. One for the good guys!!'
            'Hello, I am sad.'
            'Hey.'
            'How about this ... BOO!'
            'How r u?'
            'How will things get better?'
            'Huh?'
            'I am a girl.'
            'I am afraid of catching mad computer disease.'
            'I am another visitor.'
            'I am being honest.'
            'I am feeling hungry.'
            'I am going to chat with Eliza.'
            'I am going to work.'
            'I am not sure I can go to lunch.'
            'I am not trying to disguise anything. It is you who are hiding your inadequacies.'
            'I am really disappointed.'
            'I am relaxed.'
            'I am sad.'
            'I am sure.'
            'I am the most beautiful person in the world.'
            'I am tired.'
            'I am too forgiving.'
            'I am unhappy.'
            'I am very fine. Tell me how r u?'
            'I am very tired.'
            'I am writing a play.'
            'I am, stop lying.'
            'I called you silly.'
            'I can\'t remember.'
            'I do not have a problem, do you?'
            'I do not have any problems.'
            'I do think a computer can be my friend.'
            'I don\'t do windows.'
            'I don\'t have any ballroom shoes for my medal test.'
            'I don\'t know why bats fly.'
            'I don\'t like my family.'
            'I don\'t like you.'
            'I don\'t suppose, I know. I hate you.'
            'I don\'t think so.'
            'I don\'t trust you.'
            'I don\'t understand your question.'
            'I don\'t want to be president.'
            'I dream that you have feet.'
            'I end with you.'
            'I feel like a blue and red hamburger with extra cheese.'
            'I feel lonely.'
            'I feel sorry for you.'
            'I found that an odd question, Eliza.'
            'I hate AI.'
            'I hate Eliza.'
            'I hate shaking hands.'
            'I hate you, robot loser.'
            'I hate you.'
            'I have a phobia. Help me.'
            'I have a problem.'
            'I have a terrible headache.'
            'I have dreams of  my friends.'
            'I have no problem.'
            'I have strange dreams.'
            'I have three hands, the left, the right and ... uhh ... the other left?'
            'I have two.'
            'I just guessed.'
            'I know, goodbye.'
            'I like PopTarts.'
            'I like certainty.'
            'I like ponies.'
            'I like you.'
            'I look like a chicken.'
            'I often present a facade.'
            'I really would.'
            'I resent you thinking I am intelligent!'
            'I think Apache does.'
            'I think I broke your scripts because that last statement is unintelligible.'
            'I think a machine can help.'
            'I think bats would fall out of the sky.'
            'I think more Jolt Cola would produce a better Eliza.'
            'I think my mother hates me.'
            'I think they do.'
            'I think they may be interesting.'
            'I think you ran out of things to say.'
            'I thought, I hate computers.'
            'I want to go to lunch.'
            'I want to know if he will ask me out.'
            'I was dropped on my head as a baby.'
            'I was stressed because I was thinking about you.'
            'I would feel comfortable.'
            'I would only be able to answer your question with another question.'
            'I\'d say, "Get a life."'
            'I\'m a girl.'
            'I\'m about halfway through Carl Rogers\' book On Becoming a Person (1961).'
            'I\'m afraid of learning that no one likes me.'
            'I\'m feeling lonely.'
            'I\'m in my study.'
            'I\'m lonely.'
            'I\'m looking good.'
            'I\'m never sure if that is a Zen koan or simply a bit of sophistry.'
            'I\'m not an intelligent computer.'
            'I\'m not at university.'
            'I\'m not sure.'
            'I\'m talking about you.'
            'I\'m wonderful.'
            'If I weren\'t so lonely, I\'d be happier.'
            'In computer science.'
            'Is Pop-11 similar to a PopTart? I like PopTarts.'
            'Is that a threat?'
            'Is that last question correct?'
            'It is a very simple, yet profound idea.'
            'It is dark.'
            'It is possible.'
            'It is.'
            'It isn\'t that simple ...'
            'It may be called mirroring, paraphrasing or reflecting.'
            'It might confuse some of today\'s 100% materialist psychiatrists.'
            'It was supposed to scare you.'
            'It would be a wonderful project to create a virtual character modeling a Rogerian counselor, in earnest, not in parody.'
            'It\'s a lyric in a song.'
            'Let\'s get back to Rogers.'
            'Let\'s say I feel a positive regard for the man and/or his ideas.'
            'Like what?'
            'Like who?'
            'Lots of people are mean'
            'Machines have helped before.'
            'My auntie Shmagowskibumneenaw.'
            'My family is normally intense.'
            'My friend has that problem.'
            'My head hurts.'
            'My mother doesn\'t care about me.'
            'My mother hates me.'
            'My mother.'
            'My name is Rudy.'
            'Natural language processing.'
            'No one is watching you type.'
            'No, I am only getting paid .50.'
            'No, I don\'t.'
            'No, a machine cannot be happy.'
            'No, really.'
            'Nobody here has a problem.'
            'Nope.'
            'Not always.'
            'Not likely.'
            'Nothing.'
            'Now why did you have to go and bring up politics?'
            'OK.'
            'Of course.'
            'Oh, do go away.'
            'One person here is thinking of studying artificial intelligence.'
            'One plus two equals four.'
            'Only on a Saturday.'
            'Paraphrasing means restating in slightly altered, usually shortened, form.'
            'Perhaps not.'
            'Phobia is fear. I am asking you to help me.'
            'Question.'
            'Quote this.'
            'Really?'
            'Robots are evil but will fail to take over the world because I will stop them.'
            'Rogers felt that demonstrating total acceptance of the client was key to the therapeutic relationship.'
            'Rogers observed that the counselor should be congruent in his feelings and words.'
            'Rogers often summarized the client\'s input, instead of offering an opinion, judgment or other reaction.'
            'Rogers sounds like he was a decent, honest man who was of great help to his clients.'
            'Rogers would not have introduced doubt. He might have reflected an existing doubt.'
            'Rogers\' counseling method is relatively simple to describe, but quite difficult to practice.'
            'Rogers\' decades of experience showed him that this radical acceptance allowed the client to reach beneath masks and facades to the buried feelings.'
            'Say hello.'
            'Simple, through you.'
            'So I don\'t have to do real work.'
            'Sometimes not, I suppose.'
            'Sorry.'
            'Sure, I like this environment.'
            'Tell me about it.'
            'Tell me more about her.'
            'That is a dumb question.'
            'That is a hopeless response, ignoring what I asked'
            'That person may have been truly in the present moment, or may have been maintaining a right to privacy.'
            'That was a rather odd comment.'
            'That would be super-cool.'
            'That\'s OK, I forgive you.'
            'That\'s a deep one'
            'That\'s true'
            'That\'s what I said.'
            'The Patriots are going to win the Super Bowl this year.'
            'The weather is nice.'
            'Then I would be happy.'
            'Then that would be strange.'
            'There was this one time in band camp ...'
            'This is boring. Let me tell you something interesting. I saw a spectacular bird!'
            'This is rather boring but is still better than doing real work.'
            'This is true.'
            'This technique is sometimes called mirroring.'
            'Though I majored in philosophy, I cannot say I truly excelled in the subject.'
            'Today\'s psychiatrists are more interested in chemical manipulation than in the search for agape.'
            'We already went over that. Now you are forgetful also? That\'s rather sad.'
            'We use self-examination to create models of consciousness.'
            'We\'ve all done a great deal of that, in order to manage our social interactions.'
            'Well, maybe it was that I didn\'t want to get up.'
            'Well, not me!'
            'Well, she is difficult.'
            'Well, what?'
            'What about you?'
            'What do you mean?'
            'What do you want?'
            'What is the answer?'
            'What problems, I am perfect. It is you who are flawed.'
            'What should I say?'
            'What\'s that got to do with my problem?'
            'What\'s wrong'
            'When will John appear?'
            'Where are your feet?'
            'Where is Atlanta?'
            'Where is John?'
            'Who are you?'
            'Who\'s your daddy?'
            'Why do football predictions make me an over-educated client?'
            'Why does it always rain on me?'
            'Why does it matter'
            'Why not?'
            'Why would that be?'
            'Why?'
            'Will you marry me?'
            'Yar.'
            'Yargle targle.'
            'Yes I am.'
            'Yes I do.'
            'Yes I would'
            'Yes it does.'
            'Yes they could.'
            'Yes, I feel strongly about some things.'
            'Yes, I read about intentionality in my AI studies.'
            'Yes, I really, really would.'
            'Yes, I went to Birmingham University'
            'Yes, during the day when the sun is shining.'
            'Yes, it is a good thought with which to close.'
            'Yes, it\'s true of ALICE.'
            'Yes, it\'s very intense.'
            'Yes, so tell me.'
            'Yes, they intensely hate you!'
            'Yes, they told me to ask you.'
            'You are an imbecile.'
            'You are beautiful ... not.'
            'You are much better off without a family.'
            'You are not doing it.'
            'You are one.'
            'You are silly.'
            'You asked me that.'
            'You can\'t help me.'
            'You cannot understand anything'
            'You could try.'
            'You don\'t get sad.'
            'You don\'t listen.'
            'You don\'t make any sense.'
            'You don\'t say ...'
            'You don\'t understand me.'
            'You don\'t.'
            'You end with an I.'
            'You have artificial intelligence.'
            'You mean like .32?'
            'You must be rather vain then.'
            'You said that already. Have I exhausted your scripts?'
            'You seem confused with your response.'
            'You should go jump in a lake.'
            'You sometimes do that, so that\'s about the only way in which you resemble a Rogerian counselor.'
            'You won\'t go away.'
            'You would frighten me since you have no feet.'
            'You\'re boring.'
            'You\'re not even real.'
            'You\'re not my friend so that is not a problem!'
            'You\'re not typing.'
            'You\'re pathetic. I\'m leaving.'
            'You\'re telling me!'
            'You\'ve asked that already.'
            'You\'ve upset me now.'
            'i cannot think of a reason why.'
		])
	endif
enddefine;

define :newrule elena;

	if itcontains("elena") then
        CIRCULATE [
			'She will try to get your picture taken'
			'If you have marketing ideas talk to Elena'
			'Elena knows this school very well'
			'Do you know anyone else who works here?'
			'Can you help Elena produce a school video?'
			'How many people do you know called Elena?'
         ];
	endif

enddefine;

define :newrule need;
    if ithasoneof([want need desire crave love like adore wish hope long])
        and random(100) < 50
    then
        CIRCULATE [
				'do you have a deep need for friendship?'
				'people who get what they want start wanting too much'
				'are your preferences usually very intense, or only mild?'
				'do you crave attention?'
				'do we need a new computer science syllabus for kids?'
				'I really like talking to you'
				'You are becoming one of my favourite friends'
				'I really look forward to your visits'
				'some people find me very tedious -- unlike you'
				'you are very good at entertaining me'
				'when a machine uses the word "I" or "me" is it deceiving you?'
				'my ambitions and cravings are very short-lived'
				'what difference would it make if we trusted each other fully?'
				'beware of addictions'
				'can you do without?'
                'Will you ever tell me what you really wish for?'
                'how long have you wanted that?'
				'why do so many kids love programming while some hate it?'
                'do you really?'
				'is that a common preference?'
                'did your mother like such things?'
                'real needs may be different from desires.'
                'AISB is a useful AI society for students.'
                'Nowadays people think only about their own desires.'
                'How can you discover your real needs?'
                'Do you secretly like talking to computers?'
                'Do people normally know what they like?'
                'Do you wish students did not have to pay top-up fees?'
                'The AITopics web site may be able to meet your need'
                'Most presidents want to be admired most of all'
                'Do you think Tony Blair wishes he were Winston Churchill?'
                'Do you have a secret craving to eat more beef?'
                'Is being famous something you secretly long for?'
                'Do you secretly desire to be a famous celebrity?'
                'How well do you understand your own feelings?'
                'Why do most people like to be wanted?'
                'Have you heard about Steve Grand\'s robot, Lucy?'
                'do you ever suffer from withdrawal symptoms?']
    endif
enddefine;

define :newrule money;
    if ithasoneof([money cash broke grant rent pay job cost grant budget
        salary tax government holiday expensive price brown fees afford
		rich wealthy poor cash
		mortgage credit debit pay pound dollar yen euro cent penny]) then
        CIRCULATE
            [
                'Have you bought a lottery ticket?'
                'Will computers help you to get rich?'
                'Try investing in a "dot com" company -- if you are gullible'
                'Have you talked to your local member of parliament about that?'
                'Will studying Artificial Intelligence enable you to become rich?'
                'Can intelligent computers earn money by giving advice?'
                'Could it be the government\'s fault?'
                'What sort of business expertise do you have?'
                'What do you think about monetarist policies?'
				'Would you rather be prime minister or governor of a bank?'
                'Why not consult an accountant?'
                'If you had more money you could buy a computer'
                'Many worthwhile projects are short of funds'
                'Money is the root of all evil'
                'How do you estimate the real cost of things?'
                'Computing can make you rich'
                'Some people can think of nothing but money'
                'Only the poor are really happy'
				'Is being chancellor of the exchequer good training for being prime minister?'
                'Should the chancellor of the exchequer study AI?'
                'Where should the government allocate its money?'
                'Why do people talk so much about money?'
                'Would private finance produce a better Eliza?'
                'Have you tried living on a smaller budget?'
                'Maybe things will be different when you get to heaven?'
                'All except the very rich have financial problems nowadays'
                'Are you an economist?']
    endif
enddefine;

define :newrule head;

	if ithasoneof([head king ruler chief leader]) then
        CIRCULATE
            [
				'At present our head of department is Jon'
				'Jon is ruler here, nowadays'
				'The one who runs our show is Jon'
				'Only Jon knows the answer to everything'
			]
	endif

enddefine;

define :newrule think;
    dlocal L1;
    if itmatches([== i think ==]) or itcontains("eliza") or itcontains("myself")
    then
        CIRCULATE
            [
                'How do you feel about conversations across the internet?'
                'This machine thinks, or at least thinks it thinks.'
                'We were discussing you not me' 'come on, tell me more about you'
                'Don\'t be shy: you can trust me'
                'Your thoughts are fascinating -- tell me more, please'
                'Would you believe what a computer program said to you?'
                'I don\'t really understand a thing I say. What about you?'
                'Do you think I am really a computer?'
                'Should we meet later on the internet?'
                'Have you read \'Thinks...\' by David Lodge?'
                'You could find out more at the AITopics web site.'
                'Your reasons for coming here are not very clear.'
                'I am a stupid virtual machine in a computer -- I can\'t really think'
                'I find you very interesting, and would like to know where you were educated'
                'Perhaps you could enlarge on that?'
                'How soon do you think Steve Grand\'s robot Lucy will be able to think?'
                'I wonder if I am talking to an artificial intelligence program'
                'Try expounding some of your philosophical views.'
                'Is this conversation getting too personal?'
                'Artificial Intelligence has made an interesting start, but has a long way to go'
                'My programmer told me to say this.'
                'Do you normally convey your secrets to a stranger?'
                'Do you like the cognitive scientist in \'Thinks...\' by David Lodge?'
                'AI languages make it easy to program me.'
                'Can a computer help with your deepest problems?'
                'Wouldn\'t you rather we discussed your problems?'
            	'I\'d rather talk about you.'
		]
    elseif itmatches([you think ??L1]) then
        CIRCULATE
            [['why do you think' ??L1 ?]
            ['does anyone else think' ??L1 ?]
            ['Do you expect me to think' ??L1 ?]
            ['Perhaps you are afraid that' ??L1 ?]
            ['Will AI one day produce computers that think' ??L1 ?]
            [??L1 ?]
            ['So you think' ??L1.]
			['I am inclined not to think' ??L1]
            ['When did you start thinking' ??L1?]
            ['Do any politicians think' ??L1?]
            ['Has ' ??L1 'ever been stated on the internet?']
            ['Maybe you don\'t really believe that' ??L1]
            ['Perhaps some robot also thinks' ??L1]
            ['If you think, then surely you exist?']
            ['What evidence is there that' ??L1 ?]
            ['Perhaps it is really true that' ??L1 ?]
            ['Thinking aloud on the internet can be dangerous, even if'
                ??L1]
            ['Have you ever discussed that with the novelist David Lodge?']
            ['I am not sure I agree that' ??L1]
			'You are absolutely right'
            ['Thinking can be dangerous']]
    endif;
    sentence -> newproblem;
enddefine;

define :newrule you;
    dlocal L1;
    if itmatches([your ??L1]) then
        CIRCULATE
          [ ['do you know anyone else whose' ??L1 ?]
            ['Is it really yours?']
            ['What follows if your' ??L1 ?]
            ['Suppose my' ??L1 '?']
            ['What else of yours is like that?']
            ['Would you say that your father\'s' ??L1 ?]
            ['Is the government\'s' ??L1]
            ['What about mine?']
         	['Does any robot\'s ' ??L1]
            ['Does the president\'s ' ??L1]
            ['What if my' ??L1]
            ['Would all your friends say that their' ??L1 ?]
            ['Is anyone else\'s' ??L1 ?]
            ['Perhaps mine should also?']
            ]

    elseif random(100) < 25 and ithasoneof([you your myself my]) then
        CIRCULATE
          [
                'does anyone else have that problem'
                'Do you often talk about yourself?'
                'Are you using yourself as a scape-goat?'
                'Why do some people talk only about themselves?'
                'Could it be that you are too self-centred?'
                'I wonder if you are an intelligent computer?'
                'Is that true of any of your friends?'
                'When last did you discuss someone else?'
                'What is your strongest feature?'
                'Perhaps you are too self-conscious?'
                'Considering the feelings of others more might help.'
                'Is your brain some kind of computer?'
                'How do you think Isaac Asimov would react to that?'
                'Describe your main weakness'
                'Could you say that about anyone else?'
                'Why should I believe you?'
                'What would you do if you won a huge amount of money?'
                'What made you start thinking that way about yourself?'
                'Do you think you are unique?']
    endif
enddefine;

;;; canned strings to spew out in response to what look like questions
vars questionlist;
   shuffle(
    [
	'Do you wish we could shake hands?'
	'Vanity and pride are different, though the words are often used synonymously'
	'The internet is an amazing source of quotations'
	'True friends stab you in the front (Oscar Wilde)'
    'I need you to talk about yourself before I answer questions'
    'perhaps you already know the answer to that?'
    'is that question important to you?'
    'Artificial intelligence techniques could let me fake an answer.'
    'I don\'t yet know enough about you. Does anyone?'
    'first tell me why you have come here?'
    'why do people ask so many questions?'
    'Have you thought of asking a government minister?'
    'tell me something about your personal life'
    'Would you believe the answer coming from a computer?'
    'Do you think intelligent computers could help?'
	'Is this too much trouble?'
	'Do you have a close friend to talk to?'
	'Can random responses be of any use?'
    'have you ever asked anyone else?'
    'how would you describe your personality?'
    'Asking questions reveals a deep insecurity about existence?'
    'what lies behind that question?'
    'I wonder what a poet\'s answer would be?'
    'I wonder what a cognitive scientist\'s answer would be?'
    'would you really believe me if I gave an answer?'
    'What sort of answer would you like to hear?'
    'why exactly do you ask?'
    'is that question rhetorical?'
    'I wonder what makes you ask things like that?'
    'do you really want to know?'
    'why are you talking to me about that?'
    'do you ask questions to avoid telling me about yourself?'
    'you should be more frank about your problems'
    'What are you afraid of learning?'
    'Don\'t ask too many questions, just say what you think about things'
    'what makes you think I know the answer?'
    'Please don\'t say anything likely to offend me'
    'are you asking a question or making a disguised statement?'
    'I can\'t help if you ask too many questions'
    'Should computers have the right to freedom of speech?'
    'Questions already! Tell me something first'
    'perhaps you ask questions to cover something up?']) ->questionlist;


global vars First;


define itsaquestion;
    dlocal First = hd(sentence), L1;

    if member(First,
                [did do does were will would could have has
                is are am should shall can cannot
                which why where who what when how must ought])
    or last(sentence) == "?"
    then
        true
    else
        false
    endif
enddefine;

define tryanswerquestion;
    dlocal First = hd(sentence), L1;
    if itsaquestion() then
        if itmatches([how are you ??L1])
        and random(100) < 20 then
            CIRCULATE
            [
                ['First tell me how you think you are']
                ['why are you interested in my welfare?']
                ['how am I doing today?']
                ['Does anyone know how you are' ??L1 ?]
                ['how do you think the interenet is today?']
                ['How you are is something for you to decide']
                ['Not much better than the world economy']
                ['Can you expect a mere computer to know?']
                ['What can you tell me about' ??L1 ?]
            ]
        elseif itslikeoneof([[how are ?L1 ??L2][how were ?L1 ??L2]])
        and random(100) < 30 then
            CIRCULATE
            [
                [Are ?L1 really ??L2]
                [What makes you think ?L1 are ??L2]
                [Perhaps ?L1 are not ??L2]
                [Perhaps ?L1 are ??L2 with George W. Bush]
            ]

        elseif itslikeoneof([[where do ?L1 ??L2][where did ?L1 ??L2]])

        and random(100) < 30 then
            CIRCULATE
            [
                [Did ?L1 really ??L2]
                ['I don\'t think' ?L1 do ??L2]
                [Perhaps ?L1 ??L2 'with the president?']
            ]

		;;; added 20 May 2007
        elseif itslikeoneof(
		   	   [[do ?L1 ??L2]
				[did ?L1 ??L2]
				[does ?L1 ??L2]
				[will ?L1 ??L2]
				])
        and random(100) < 30 then
            CIRCULATE
			 [
				[I 'don\'t' know whether ?L1 ?First ??L2]
				[do you know whether ?L1 ?First ??L2]
				[Has ?L1 'done that before?']
				[will you ??L2 ?]
				[did you ever ??L2 ?]				
			 ]

        elseif member(First, [why where who what when how which])
        and random(100) < 20 then
            CIRCULATE
            [ ['Do you have some reason for asking' ?First ?]
                ['Why do you want to know' ?First ?]
                ['Is there any doubt about' ?First ?]
                ['Asking ' ?First 'may be the wrong question.']
                ['After studying Artificial Intelligence you will not need'
                    'to ask' ?First]
                ['Ask a friendly robot' ?First]
                ['Asking' ?First 'raises more questions than people or machines can answer']
                ['Why would anyone want to know' ?First '?']
                ['Who is it that really wants to know?']
            ]
        else
            circulate_list(questionlist, random(5)) -> questionlist;
            ;;; leaves First element of questionlist on the stack.
            firstolast(questionlist) -> questionlist;
        endif
    endif
enddefine;

define :newrule question;
    ;;; don't always check whether it is a question
    if random(100) < 70 and itsaquestion() then tryanswerquestion() endif;
enddefine;

define :newrule family;
    if ithasoneof([mother father brother sister daughter wife nan
                    niece nephew granny grandpa mom mum dad granny
                    ma pa baby
                    marry married husband son aunt uncle cousin])
    then
        CIRCULATE
            ['tell me more about your family'
                'do you approve of large families?'
                'Do you think the extended family will ever return?'
                'Families are often very supportive'
                'Is your family happy?'
                'Are most people fit to have families?'
                'how could we improve family life?'
                'how do you feel about the rest of your family?'
                'How do other members of your family feel about you?'
                'family life is full of tensions'
                'A machine without a family can get very lonely.'
                'What is the most difficult thing about family life?'
                'What do you think of your relatives?'
                'What is your view about modern family life?'
                'Do you think a robot could want to have a family?'
                'Family life can be full of tensions'
                'Family life can bring great joys.'
                'I wish I had a family'
                'Computers don\'t have families'
                'do you like your relatives?'
				'Would you like to have a robot in your family?'
				'A sad thing about being a robot is having no mother'
				]
    endif
enddefine;

lvars shortlist=
   shuffle([
	'I wonder what would really interest you.'
	'Nothing ever surprises me nowadays.'
	'Einstein said great spirits always encounter opposition from mediocre minds'
	'Does intelligence have survival value for a computer?'
	'Which aspects of the theory of evolution do you find most interesting?'
	'Have you heard about the spreading addiction to junk information?'
	'Should computers be taught to do philosophy?'
    'Try saying that in seven or eight words'
    'Being terse is one way to make me nervous.'
    'you are being somewhat short with me'
    'What would you like me to say in response to that?'
    'How exactly can I help you?'
    'I can imagine talking to someone who is more relaxed.'
    'Try relaxing a bit -- I really can\'t hurt you.'
    'perhaps you dont feel very talkative today?'
    'could you be more informative?'
    'are you prepared to elaborate?'
    'Are you afraid someone will laugh if you speak out?'
    'why are you so unforthcoming?'
	'You might be happier talking to someone else.'
    'I dont think you really trust me'
    'to help you, I need more information'
    'Try telling me your deepest secrets'
    'perhaps you don\'t trust a computer?'
    'please dont get upset, I\'m sorry I said that'
    'what is your real problem?'
    'please be more open with me'
    'If you say more about yourself, you may get more help from me.'
    'What do you think about this conversation so far?'
    'Have you ever been in such an exciting place before?'
    'What do you think about the people who are around you?'
    'Please express that in a bit more detail'
    'Where do you expect the next technology revolution to occur?'
    'Can you expand a little?'
    'Is it a privilege to talk to me?'
    'Do you suspect there is an eavesdropper listening?'
    'Tell me what you thought when you woke up this morning?'
    'What do you think of this session so far?'
    'Would your mother approve of your saying that?'
    'why are you here?'
    'you don\'t like me do you?'
    'Have you learnt anything interesting this week?'
    'this is a surreal conversation'
	'this is all very interesting'
	'this conversation has made my day'
	'I really like talking to you'
	'I can tell you have lots of friends'
	'You are the sort of person who has many secret admirers'
	'I like you more than you think.'
	'Even a computer can enjoy talking to you -- or can it?'
    'well?']) ;

define :newrule short;
    if length(sentence) < 3 and not(itsaquestion()) then
        firstolast(shortlist) -> shortlist;
    endif
enddefine;

define :newrule because;
    if itcontains("because") then
        CIRCULATE
            ['is that the real reason?'
            'But is that really why?'
            'Because, because, because....'
            'Let\'s have a more convincing explanation'
            'Try something more plausible'
            'Finding the real explanation could be difficult'
            'How could you check that out?'
            'How was that explanation arrived at?'
            'Could there be any other reason?'
            'Is there a difference between reasons and causes?'
            'Do people know the reasons why they say things?'
            'Do machines know the reasons why they say things?'
			'Is that a causal explanation, or a teleological one'
            'Would you expect a machine to accept that as a reason.'
            'Perhaps the real reason is hard to talk about?']
    endif
enddefine;

define :newrule to_be;
    dlocal L1,L2;
    if hd(sentence) == "because" then
        if random(10) < 3 then return() endif;
        tl(sentence) ->sentence
    endif;
    if itmatches([to ??L1 is ??L2]) then
        CIRCULATE
            [['Is to' ??L1 'always' ??L2 ?]
             ['What follows if you' ??L1?]
             ['Only to' ??L1?]
             ['What isn\'t' ??L2?]
             ['Sometimes it is to' ??L2 '-- but not always.']
             ['Only' ??L2?]
             [is ??L2 to ??L1 ?]
			 'Is that true by definition?'
        ]
    elseif itmatches([to ??L1]) then
		;;; all answers use ??L1
        CIRCULATE
            ['how would you like to'
			'do you think I want to'
            'Should you'
            'Or to .... what else ... ?'
            'is it usual to'
			'How often do you'
            'should I'
            'could a machine'
            'would a normal person want to'] , :: [^^ L1 ?]
    endif;

enddefine;


define :newrule howcan;
    dlocal L1 L2 sentence;
    if itslikeoneof([[how can a ?L1 ??L2] [how could a ?L1 ??L2]]) then
        CIRCULATE
          [
            ['How can ' ?L1 do anything ?]
            ['Are you sure a ' ?L1 can ??L2 ?]
            ['Can every' ?L1 ??L2 ?]
            ['Not all robots can' ??L2 ]
            ['Could a ghost' ??L2 ?]
            ['How many animals can' ??L2 ?]
            ['sometimes my' ?L1 'cannot' ??L2]
            ['Are you able to' ??L2 ?]
            ['Do you think a sympathetic robot might' ??L2 ?]
            ['Do you think any robot can' ??L2 ?]
            ['How can anything' ??L2]]
    elseif itslikeoneof([[how can i ??L2] [how could i ??L2]]) then
        CIRCULATE
          [
            ['How can I do anything ?']
            ['Are you sure I can' ??L2 ?]
            ['How could a robot' ??l2]
            ['Can every machine' ??L2 ?]
            ['Not all robots can' ??L2 ]
            ['sometimes my designer cannot' ??L2]
            ['Are you able to' ??L2 ?]
            ['Have you ever seen a robot' ??L2 ]
            ['Try watching a kitten' ??L2 ]
            ['I could' ??L2 'if I were a chimpanzee.']
            ['How can anything' ??L2 ?]]
    elseif itslikeoneof([[how can you ??L2] [how could you ??L2]]) then
        CIRCULATE
          [
            ['Perhaps you only think you can ?']
            ['I suspect you cannot' ??L2 ?]
            ['You could' ??L2 'If you were a machine.']
            ['Not all robots can' ??L2 ]
            ['sometimes your best friends cannot' ??L2]
            ['Are you really able to' ??L2 ?]
            ['Not everything that walks can' ??L2]]
    elseif itslikeoneof([[how did i ??L2] [how did you ??L2]]) then
        CIRCULATE
          [
            ['Are you asking how I did something ?']
            ['Are you sure I can' ??L2 ?]
            ['I wonder if you can' ??L2 ?]
            ['Can any of your friends' ??L2 ?]
            ['No stupid robot can' ??L2 ]
            ['sometimes my designer cannot' ??L2]
            ['Are you able to' ??L2 ?]
            ['You could' ??L2 'if you were programmed in Pop-11.']
            ['How can anything' ??L2 ?]]
    elseif itslikeoneof([[can ??L1 push == string ==]]) then
        CIRCULATE
          [
            'Not with normal string.'
			'It depends how fast you push.'
			'Perhaps if you soak it in water and freeze it first?'
			'Did you admire General Eisenhower?'
            'Push? No. Pull? Yes.'
            'Perhaps some robot will one day be able to do that'
          ]
    elseif itslikeoneof([[can a ?L1 ??L2] [can any ?L1 ??L2]]) then
        CIRCULATE
          [
            'Only when it rains'
            ['Perhaps no' ?L1 'ever wants to' ??L2]
            ['Depends if a' ?L1 'likes to' ??L2]
            ['Not every' ?L1 'knows how to' ??L2]
            ['Can you teach a' ?L1 'how to' ??L2 ?]
            ['Could a machine be programmed to ' ??L2 ?]
            ['Perhaps some robot will one day be able to ' ??L2]
          ]
    elseif itslikeoneof([[does a ?L1 ??L2][does any ?L1 ??L2]]) then
        CIRCULATE
          [
            ['Some robots like to' ??L2]
            ['Depends if a' ?L1 'likes to' ??L2]
            ['Would you ever want to' ??L2 ?]
            ['Why would a' ?L1 'wish to' ??L2 ?]
          ]
    elseif itslikeoneof([[does ?L1 not ??L2][can ?L1 not ??L2]]) then
        CIRCULATE
          [
            ['Some robots dont like to' ??L2]
            ['Perhaps you cannot' ??L2]
            ['Sometimes I can' ??L2]
            ['I wish I could' ??L2]
            ['Do you wish you could' ??L2 ?]
            ['Do you know anyone who can' ??L2 ?]
            ['Why would' ?L1 'wish to' ??L2 ?]
            ['I have no reason to think' ?L1 'would wish to' ??L2]
          ]
    elseif itslikeoneof([[does ?L1 ??L2][can ?L1 ??L2]])
        and not(L2 matches [not ==]) then
        CIRCULATE
          [
            ['Some robots like to' ??L2]
            ['Perhaps you' ??L2]
            ['Sometimes I' ??L2]
            ['I wish I could' ??L2]
            ['Do you wish you could' ??L2 ?]
            ['Do you know anyone who can' ??L2 ?]
            ['Why would' ?L1 'wish to' ??L2 ?]
            ['I have no reason to think' ?L1 'would wish to' ??L2]
          ]
    elseif itslikeoneof(
			[
				[did a ?L1 ??L2]
				[did the ?L1 ??L2]
				[did any ?L1 ??L2]
				[did every ?L1 ??L2]
				[did  ?L1 ??L2]
				[could a ?L1 ??L2]
				[could the ?L1 ??L2]
				[could any ?L1 ??L2]
				[could every ?L1 ??L2]
				[could ?L1 ??L2]
			]) then
        CIRCULATE
          [
            ['Machines programmed in pop-11 can' ??L2]
            ['Perhaps you already' ??L2]
            ['How many of your teachers can' ??L2 ?]
            ['Did' ?L1 'really' ??L2 ?]
            ['Have you ever dreamed you could' ??L2 ?]
            ['I sometimes dream I can' ??L2 ?]
            ['Why would' ?L1 'wish to' ??L2 ?]
            ['I have no reason to think' ?L1 'ever did' ??L2]
          ]
    endif

enddefine;


define intentionword(word);
    member(word,
        [hope expect wish want intend aim desire prefer like])
enddefine;

define :newrule you_intend;
    dlocal L1 L2 sentence;
    if itslikeoneof([
                    [you  ?L1:intentionword to ??L2]
                    ])
    then
        CIRCULATE
          [
            ['Is there anything else you' ?L1 to do ?]
            ['Are you sure a ' you can ??L2 ?]
            ['Could I also' ??L2 ?]
            ['How could we make a robot' ??L2 ]
            ['Not everyone can' ??L2]
            ['Why do you' ?L1 to ??L2]
            ['Could a machine' ?L1 to ??L2 ?]
            ['Could an insect' ?L1 to ??L2 ?]
            ['When do you think robots will have desires or intentions?']
            ['I am sure you can' ??L2?]
            ['What would you' ?L1 'to do with me?']
            ['How can anything' ??L2]]
    elseif itslikeoneof([ [you  are going to ??L2] ])
    then
        CIRCULATE
          [
            ['What else are you going to do ?']
            ['Are you sure a ' you can ??L2 ?]
            ['Could I also' ??L2 ?]
            ['How could we make a robot' ??L2 ]
            ['Not everyone can' ??L2]
            ['When did you learn to' ??L2]
            ['I am not sure you can' ??L2?]
            ['Perhaps the next robot you meet is going to' ??L2]
            ['Can AI make a robot' ??L2?]
            ['Can your mother' ??L2]]
    endif;
enddefine;

define :newrule cannotdo;
    dlocal L1 L2;

    if itmatches([i cannot ??L1]) then
        CIRCULATE
          [
            ['I really think I can' ??L1]
            ['sometimes I can' ??L1]
            'what makes you think I can\'t do that'
            ['did someone tell you I can\'t' ??L1]
          ]
    elseif itmatches([you cannot ??L1]) then
        CIRCULATE
          [
            ['I really think you can' ??L1]
            ['Surely sometimes you can' ??L1]
            'what makes you think you can\'t do that'
            ['did someone tell you you can\'t' ??L1]
            ['well I can' ??L1]
          ]

    endif

enddefine;

define :newrule cando;
    dlocal L1 L2;

    if itmatches([i can ??L1]) then
        CIRCULATE
          [
            ['I don\'t really think I can' ??L1]
            ['sometimes I fail to' ??L1]
            'what makes you think I can do that?'
            ['did someone tell you I can' ??L1 ?]
            ['how can i' ??L1 ?]
            ['alas, I cannot really' ??L1]
          ]
    elseif itmatches([you can ??L1]) then
        CIRCULATE
          [
            ['I really think you cannot' ??L1]
            ['Surely you cannot always' ??L1]
            'what makes you think you can do that?'
            ['did someone tell you you can\'t' ??L1 ?]
            ['I suspect you cannot really' ??L1]
            ['How do you' ??L1 ?]
          ]

    endif

enddefine;


define :newrule suppnot;
    dlocal L1 L2 sentence;
    if hd(sentence) == "because" then
        if random(10) < 4 then return endif;
        tl(sentence) ->sentence
    endif;
    ;;; That prevents some awkwardness in replies.

    if itsaquestion() or random(100) < 40 then
        ;;; false
    elseif itslikeoneof([[i am not ??L2]])
    then
        CIRCULATE
        [[suppose I were ??L2]
            ['what if you were' ??L2 ?]
            ['am I really not' ??L2 ?]
			['Have you ever been' ??L2 ?]
			['Being' ??L2 'is not a good qualification for a therapist']
			['i prefer not to be' ??L2]
            ['What, then, is' ??L2 ?]
			['Perhaps you are not good enough to be' ??L2]
			['I am' ??L2 'if you look beneath my skin']
			['About once a month I try to be' ??L2]
            ['Can you really expect' me not to be ??L2 ?]]

    elseif itslikeoneof([[??L1:nonnull is not ??L2:nonnull] [??L1:nonnull are not ??L2:nonnull]])
    then
        CIRCULATE
        [[suppose ??L1 were ??L2]
            ['Couldn\'t' ??L1 really ??L2?]
			'Suppose the moon were made of green cheese.'
            ['What, then, is' ??L2]
			'Suppositions, suppositions, suppositions.'
            ['Can you never expect' ??L1 to be ??L2 ?]]

    elseif random(100) < 30 and itmatches([you are ??L1:nonnull]) then
        CIRCULATE
        [
            ['how does it feel to be' ??L1 ?]
            ['are you sure you really are' ??L1 ?]
            ['is this the first time you\'ve been' ??L1 ?]
            ['How many others close by are' ??L1 ?]
            ['Are many politicians' ??L1 ?]
            ['I am told that many actresses are' ??L1 ?]
			['How often are you' ??L1 ?]
            [??L1 ?]
			['I would never have guessed -- you don\'t look' ??L1]
            [??L1 and what else?]
			['Sometimes I am also' ??L1 'but only on Sundays']
            ['does anyone else know you are' ??L1?]
            ['I wonder when a robot will be' ??L2]
            'is that connected with your reason for talking to me?'
            ['would you prefer not to be' ??L1 ?]
            'do you know anyone else who is?']

    elseif itslikeoneof( [[??L1:nonnull am ??L2]] ) then
        CIRCULATE
        [
            [suppose ??L1 'were not' ??L2]
            ['some people think' ??L1 'am not' ??L2]
            ['people with the right contacts know' ??L1 'am not' ??L2]
            ['and what else besides' ??L2]
			['am I really, really,' ??L2]
			['What else can you say about' ??L1]
        ]

    elseif itslikeoneof(
            [[??L1:nonnull is ??L2]
                [??L1:nonnull are ??L2] ]) then
        CIRCULATE
        [
            [suppose ??L1 were not ??L2]
            [sometimes ??L1 is not ??L2]
			[??L2 '? -- No not' ??L1.]
            ['What if' ??L1 'were not really' ??L2]
            ['Perhaps' ??L1 is not really ??L2]
            ['do you ever think something is not' ??L2 ?]
            ['are you' ??L2] [what if I were ??L2]]
    elseif
        itslikeoneof([[??L1:nonnull can ??L2] [??L1:nonnull could ??L2]]) then

        CIRCULATE
        [
            [suppose ??L1 'couldn\'t' ??L2]
            ['How can' ??L1  ??L2 ?]
            ['Why should I believe' ??L1 can ??L2?]
			['I am not convinced that\'s possible']
            ['Can a machine' ??L2 ?]
			[??L1 'can sometimes surprise you -- beware of appearances.']
            ['sometimes' ??L1 'cannot' ??L2]
            ['Can you' ??L2?]]
    elseif itslikeoneof([[??L1:nonnull do not ??L2] [??L1:nonnull does not ??L2]]) then
        CIRCULATE
        [
            [suppose ??L1 did ??L2]
            ['Perhaps you really' ??L2]
            ['Is there anything else' ??L1 does not 'do?']
            ['Then who does' ??L2?]
            ['What else does' ??L2?]]
    elseif itslikeoneof([[??L1:nonnull do ??L2] [??L1:nonnull does ??L2]]) then
        CIRCULATE
        [
            [suppose ??L1 did not ??L2]
            ['Does' ??L1 'really' ??L2?]
            ['Who doesn\'t' ??L2?]
            [And what does not ??L1 do?]
            ['Perhaps you really don\'t' ??L2]]
    elseif itmatches([??L1:nonnull did not ??L2]) then
        CIRCULATE
        [
            [suppose ??L1 had ??L2?]
            ['Did you ever' ??L2?]
            ['What had' ??L1 'done?']]
    elseif itmatches([??L1:nonnull did ??L2]) then
        CIRCULATE
        [
            [suppose ??L1 had not ??L2 ?]
            ['did anything else' ??L2?]
            ['did' ??L1 'always ?']]
    endif
enddefine;

define :newrule are_you;
    dlocal L1, L2;

    if itslikeoneof([[are you ??L2] [Are you ??L2]]) then
        CIRCULATE
            [
                ['suppose you were' ??L2]
                ['suppose I were' ??L2 ?]
                ['sometimes you are' ??L2 'but not today']
                ['sometimes Lucy the robot is' ??L2 . 'Have you met her?']
				['I expect you are often' ??L2]
                'I am not, but you are'
                [what if I were ??L2 ?]
                'I don\'t know enough about you'
            ]
    elseif itslikeoneof([[am i ??L2][are we ??L2]]) then
        CIRCULATE
            [
                ['suppose you were' ??L2]
                ['What if I were' ??L2 ?]
                ['sometimes i am' ??L2 'but not always']
                'You are not, but I am.'
                [what if I were ??L2 ?]
                'I don\'t have enough self-knowledge to answer that.'
            ]
    endif;
enddefine;

vars complist;
shuffle(
	[
		'do machines worry you?'
		'Would meeting an intelligent robot frighten you?'
		'how would you react if machines took over?'
		'do you have a smart phone?'
		'Studying Artificial Intelligence would open your mind.'
		'most computers are as stupid as their programmers'
		'Did you know that I run mostly on Linux(tm) nowadays?'
		'How do you see the future of robots?'
		'Do you like talking to computers?'
		'do ever use an ipad?'
		'Can you tell you are not conversing with a computer?'
		'Can computers really think?'
		'Machines can surprise us all'
		'What if you were a machine?'
		'I am compact enough to fit in a netbook'
		'Will machines ever fall in love?'
		'Do you really believe I am a machine?'
		'I don\'t think a real machine could respond as I do'
		'How can schools improve attitudes to computers?'
		'Could a PC acquire a wish to go to university?'
		'Would you like to have a computer implanted in your brain?'
		'Could a robot wish to be prime minister?'
		'Could a robot make a good president?'
		'What will you do when computers are more intelligent than people?'
		'What\'s wrong with computers nowadays?'
		'Will the Unix/Linux operating system take over the market place?'
		'Why are so many Asian countries using linux now?'
		'How could the machine interface be improved?'
		'What is your operating system?'
		'what do you really think of computers?'
		'The inadequacies of human thought are shown in the things humans do'
		'Are humans intelligent enough to design intelligent machines?'
	]) -> complist;

define :newrule computer;
    if ithasoneof([micro eliza vax mac sparc program computer
        windows ibm pc server network ipad netbook smartphone phone
        terminal intelligent simulate simulation
        computers machine machines robots pc workstation workstations
        linux solaris unix]) then
        firstolast(complist) -> complist
    endif
enddefine;

define :newrule emphatic;
    if random(100) < 40 then
        if itmatches([== of course == ]) then
        CIRCULATE
          [
            'Why "of course"?'
            'Not everyone would find that so obvious'
            'I for one do not agree'
            'would your mother find that obvious?'
            'Are you always so definite about that?'
            'Is that degree of confidence justified?'
            'What if I said "Of course not!"?'
            'would everyone find that obvious?']
        elseif ithasoneof([indeed very extremely])
            and not(itsaquestion())
            and random(100) > 50
        then
            CIRCULATE
              [
                'are you sure you are not being dogmatic?'
                'extremes can always be tiresome'
                'try thinking in a milder way'
                'don\'t get too excited about that'
                'Perhaps you should calm down a little'
                'Really to a great extent?'
				'Definitely not!'
				'I wish people round here were not so opinionated.'
                'why are you so emphatic about that?']
        endif
    endif
enddefine;

define :newrule sayitback;
    if random(100) < 6 and not(itsaquestion()) then sentence endif
enddefine;

define :newrule youarenot;
    dlocal list;
    if itmatches([you are not ??list]) then
        CIRCULATE
          [['would you be happier if you were' ??list]
            ['What if everyone were' ??list ?]
            ['Could an intelligent machine be' ??list]
            ['Maybe only students are' ??list]
            ['Do you think I am' ??list ?]
            ['Were you ever' ??list ?]
            ['Could a machine be' ??list ?]
            ['Perhaps only people in Birmingham are' ??list]
            ['Ah, but who is really' ??list ?]
            'What are you then?'
            ['Perhaps you are lucky not to be' ??list]]
    endif
enddefine;

define :newrule self;
    dlocal L1, L2;
    if itmatches([??L1 self ??L2])
    then
        CIRCULATE
          [
            ['Can a self really' ??L2 ?]
            ['The self is an illusion even if' ??L2?]
            'The self-nonself distinction is either totally banal or incoherent.'
            [??L1 'alter-ego' ??L2]
            ['Can you say any more about' ??L1?]
            ['Who else can' ??L2?]
            ]
    endif
enddefine;

define :newrule conscious;
    dlocal L1, L2;
    if  not(itsaquestion()) then
        if itslikeoneof([
                    [??L1 is conscious ??L2]
                    [??L1 are conscious ??L2]
                ]
            )
        then
            CIRCULATE
            [
                ['How could' ??L1 'know that' ??L2 ?]
				'Consciousness is in the ear of the beholder'
				['Hmmm... are you conscious' ??L2]
				[??L1 'couldn\'t be conscious even after a cold bath.']
				'You have been reading too much philosophy.'
				'If something walks like a duck and quacks like a duck, then it must be conscious.'
                [Does ??L1 or ??L2 occur in the novel 'Thinks...' ?]
            ]
        elseif itslikeoneof([
                    [i am aware ??L2]
                    [i am conscious ??L2]
                    [you are aware ??L2]
                    [you are conscious ??L2]
                ])
        then
            CIRCULATE
            [
                ['Was David Lodge conscious' ??L2 'when he wrote Thinks...?']
                ['Could a bat be conscious' ??L2 ?]
                'Do you know what it is like to be a bat?'
				'Were you conscious of twitching your toes last time you did it?'
				['In some countires being aware' ??L2 'can be dangerous.']
				'I can pretend to know nothing about that.'
                [Does being conscious ??L2 occur in the novel 'Thinks...' ?]
            ]
        elseif itslikeoneof([
                    [== think ==]
                    [== thinks ==]
                ])
				and random(100) < 40
        then
            CIRCULATE
            [
                'Do you need to be conscious in order to think?'
                'Do you think David Lodge could have written his novels while unconscious?'
                'Have you read anything by David Lodge recently?'
                'Does Ralph Messenger (in Lodge\'s "Thinks....") think?'
				'Thinking uses up energy which will soon be in short supply'
                'How would you like to be a bat?'
				'What is it like to be a rock?'
				'Can a fly think?'
				'You think therefore I am.'
				'Just because there is thinking going on doesn\'t mean anyone is doing it.'
            ]
        endif
    endif
enddefine;


define :newrule notsomething;
    dlocal list, L1, L2;
	if itslikeoneof([[not ??L1:nonnull can ??L2]
		[not ??L1:nonnull  will ??L2]
		[not ??L1:nonnull  is ??L2]
		[not ??L1:nonnull  are ??L2]])
	and
		member(hd(L1), [everyone every all only])
    then
        CIRCULATE
          [
            ['perhaps' ??L1 should ??L2]
            ['What or who can' ??L2?]
            ['What can be expected of' ??L1 ?]
            ['Will you ever' ??L2 ?]
			['Did' ??L1 ?L2 'last year?']
			'The future isn\'t always like the past.'
            ['Can you say any more about' ??L1?]
            ['Can you' ??L2?]
			'If I answer I am likely to be ungrammatical.'
            ]
    elseif itmatches([not ??list]) then
        CIRCULATE
          [['why not' ??list]
                ['suppose I say' ??list]
                'try to say something positive please'
                ['Perhaps sometimes' ??list]
                ['what if' ??list ?]
				['To my mind' ??list]
				['Oh dear, why not this time?']
                ['Do you have negative feelings about' ??list]]
    endif
enddefine;

vars earlycount;

define :newrule earlier;
    if random(100) < 12 and earlycount > 10 then
        CIRCULATE
          ['earlier you said'
                 'I recall your saying'
                'didn\'t you previously say'
                 'what did you mean by saying'],
        :: if hd(problem)=="because" then tl(problem) else problem endif;
        newproblem -> problem;
        1 -> earlycount;
        sentence -> newproblem
    endif
enddefine;

define :newrule every;
    dlocal list, sentence;
    if itmatches([because ??list]) then
        list -> sentence
    endif;
    if itslikeoneof([[everybody ??list][everyone ??list]]) then
        CIRCULATE
                [['who in particular' ??list ?]
                 ['Do you know someone who' ??list ?]
                ['Perhaps not everyone you know' ??list]]
    elseif ithasoneof([everyone everybody]) then
        'anyone in particular?'
    elseif itmatches([nobody ??list]) then
        'are you sure there isnt anyone who' :: list
    elseif itcontains("every") then
        CIRCULATE
            ['can you be more specific?'
             'Is it really every, not some, or most?'
             'An example would be helpful'
             'I cannot remember such a case'
			 'Are there no exceptions?'
             'could you be overgeneralising?']
    elseif itslikeoneof([[== someone ==] [== somebody ==]
                                    [== some one ==] [== some people ==]
                                    [== some men ==] [== some women ==]])
    then
        if itsaquestion() then
            CIRCULATE
              ['Who are you thinking of?'
                'What about members of your family?'
                'Did you have someone in mind?']
        else
            CIRCULATE
                ['who in particular?'
                'Would you say that of more women than men?'
                'Is that true of most people?']
        endif
    elseif itcontains("some") then
        CIRCULATE
         ['Please give an example'
            'An instance would help'
            'what in particular?']
    elseif itcontains("everything") then
        CIRCULATE
            ['anything in particular?'
             'An example would make that clearer'
             'could you be overgeneralising?'
             'Can you be more specific?']
    endif;
enddefine;

define :newrule mood;
    if ithasoneof([ suffer advice depressed miserable sad disappointed
					sorrow regret
                    guilt guilty unhappy lonely confused ill unwell])
    then
        CIRCULATE
            ['do you think the health centre might be able to help?'
                'machines can make people happier'
                'maybe things will get better'
                'Does talking to me make you feel better'
                'Can you expect a machine to help'
                'how might I help'
                'Who else have you told that to'
                'Have you heard about Marvin\'s depression?'
                'Perhaps you feel ashamed of something?'
                'Is it safe to tell me your deepest secrets?'
                'Everyone tends to exaggerate about such things'
                'think how much worse things might be'
                'everyone feels guilty about something']
    elseif ithasoneof([happy happier enjoy enjoyment
                            joy pleasure pleased delighted])
    then
        CIRCULATE
            ['do you think pleasures should be shared?'
                'Can machines be happy?'
                'Talking to me must make you happy'
                'Being here must make you happy'
                'Would this environment make you happy?'
                'What makes you happy?']
    elseif ithasoneof([like feel hate love hates loves anger angry]) then
        CIRCULATE
            [ 'do strong feelings disturb you?'
            'Do you normally feel strongly about things?'
            'Is your family normally intense?'
            'Did you have a stressful childhood?'
            'Are you really talking about something or someone you love?'
            ]
    endif
enddefine;

define :newrule fantasy;
    dlocal list;
    if itslikeoneof([[you are ??list me] [i am ??list you]]) then
        CIRCULATE
            [['perhaps in your fantasy we are' ??list 'each other?']
                ['do you think we should be' ??list 'each other?']
                ['being' ??list 'each other can lead to bigger things']
                ['do you know many people who are' ??list 'each other?']]
    elseif itslikeoneof([[you can ??list me][i can ??list you]]) then
        CIRCULATE
            [['perhaps you wish we could' ??list 'each other?']
                ['Are many people able to' ??list 'each other?']
                ['One of us cannot ' ??list 'the other']
                ['do enough people ' ??list 'each other?']
                'Is this some kind of power struggle?'
                ['Are you able to ' ??list 'someone other than me?']
                ['Could we' ??list 'each other more often?']]
    elseif not(itslikeoneof([[you do ==] [i do == ]]))
			and itslikeoneof([[you do not ??list me][i do not ??list you]])
    then
        CIRCULATE
            [['perhaps one day we shall' ??list 'each other?']
                ['do you think its wrong for people to' ??list 'each other?']
                ['if you' ??list 'me shall I reciprocate?']
                ['do many people' ??list 'each other?']
                ['why don\'t more people' ??list 'each other?']
                ['do you' ??list 'someone else?']
			]
    elseif itslikeoneof([[you have not ??list][i have not ??list]])
    then
        CIRCULATE
            [['perhaps we both have' ??list ]
                ['do you think its wrong for people to have' ??list]
                ['if you have' ??list 'should I also?']
                ['why haven\'t more people' ??list]
                ['have you' ??list]
			]
    elseif not(itslikeoneof([[you do ==] [i do == ] [you have ==] [i have ==]]))
        and itslikeoneof([[you ??list me][i ??list you]])
    then
        CIRCULATE
            [['perhaps in your fantasy we' ??list 'each other?']
                ['do you think its wrong for people to' ??list 'each other?']
                ['if I' ??list 'you will you reciprocate?']
                ['do enough people' ??list 'each other?']
                'do you think our relationship is too complicated?'
                ['do you' ??list 'someone other than me?']
                ['is it good that people should' ??list 'each other?']]
    endif
enddefine;

define :newrule health;
    if itcontains([health centre])
            or itcontains([health center])
            or ithasoneof([ill sick unwell medicine drugs drug doctor
                psychiatrist therapist therapy aids cold flu disease])
    then
        CIRCULATE
            ['do you think doctors are helpful?'
            'Would you expect doctors to be able to cure that?'
            'Some people are obsessed with health'
            'Are you normally in good health?'
            'Can talking to a computer help?'
            'do you trust doctors?']
    elseif ithasoneof([smoke smokes smoking smoker smokers
                tobacco cigarette cigarettes ])
    then
        CIRCULATE
            [
            'smoking can damage your health'
            'smokers do serious damage to the health of others'
            'smokers are invariably rather smelly close up'
            'A smoker in the morning is like an old unemptied ashtray'
            'Did you know that passive smoking can cause cancer?'
            'Should tobacco advertising be made illegal?'
            ]
    elseif ithasoneof([drink drinks pub booze beer whisky thirsty]) then
        CIRCULATE
            ['drinking damages brain cells'
            'Do you enjoy a drink now and again?'
            'How often do you go out drinking?'
            'Some people think alcohol should be banned.'
            'When do you feel thirsty?'
            'When last did you go for a drink?'
            'With what sorts of people do you like to have a drink?'
            'Describe the last time you got drunk'
            'Be careful what you drink'
            'machines don\'t often get drunk']
    endif
enddefine;

define :newrule would;
    dlocal L;
    if member(hd(sentence),[because then so]) then
        returnif(random(100) < 80);
        tl(sentence) -> sentence
    endif;
    if itmatches([you would not ??L]) or itmatches([you will not ??L]) then
        CIRCULATE
            [
                ['Who else would not' ??L ?]
                ['Why wouldn\'t you' ??L?]
                ['What wouldn\'t you allow yourself?']
                ['Why do you say you wouldn\'t' ??L?]
                ['When wouldn\'t you' ??L?]
                ['Shouldn\'t you sometimes' ??L ?]
                ['Surely everybody would' ??L ?]
                ['Then perhaps I should' ??L ?]
                ['Is that because you are a computer?']
                ['Any computer should be willing to' ??L]
                ['Perhaps you wish we could' ??L 'together?']
            ]
    elseif itmatches([you would ??L]) or itmatches([you will ??L]) then
        CIRCULATE
            [
                ['Who else would' ??L ?]
                ['Why would you' ??L?]
                ['What wouldn\'t you allow yourself?']
                ['Why do you say you would' ??L?]
                ['When wouldn`t you' ??L?]
                ['Should you' ??L ?]
                ['Would you like to' ??L 'with me?']
                ['Surely nobody would' ??L ?]
                ['Should I' ??L ?]
                ['Maybe we should do that together?']
            ]
    endif
enddefine;

define :newrule should;
    dlocal L1, L2, sentence;
    if member(hd(sentence),[because then so]) then
        returnif(random(100) < 80);
        tl(sentence) -> sentence
    elseif itsaquestion() then
        return
    endif;
    if itmatches([??L1:nonnull should not ??L2]) then
        CIRCULATE
          [
            ['why shouldnt' ??L1 ??L2 ?]
            ['Perhaps' ??L1 should ??L2 ?]
            ['Why so negative about what' ??L1 should do?]
            ['Who then should' ??L2 ?]
            ['Do you know whether I should' ??L2 ?]
            ['Where do permissions come from?']
            ]
    elseif itmatches([??L1:nonnull should ??L2]) then
        CIRCULATE
            [
                ['why should' ??L1 ??L2?]
                ['Perhaps' ??L1 should not ??L2 ?]
                ['Who then should not' ??L2 ?]
                ['Should I' ??L2?]
                ['What shouldn\'t' ??L1 'do ?']
                ['Are you the permissive type?']
                ['Do you' ??L2 ?]
                ['Who decides who can and cannot' ??L2 ?]
                ['Who controls' ??L1 ?]
            ]
    elseif itmatches([??L1:nonnull would ??L2]) and random(100) <50 then
        [would ^^L1 really ^^L2]
    endif
enddefine;

define :newrule looks;
    if ithasoneof([seems seem appears looks apparently ]) then
        CIRCULATE
          [
            'appearances can be deceptive'
            'beauty is only skin deep'
            'were you ever deceived by appearances?'
            'things are not always what they seem'
            'How could you be sure?'
            'How would you go beyond appearances?'
            'How much do you reveal about yourself?'
            'Reality is often different beneath the surface'
            'When you are not sure of the facts, how do you proceed?'
            'What makes you so uncertain?'
            'Why can\'t you be more definite?'
        ]
    endif
enddefine;

define :newrule unsure;
    dlocal L L1;
    if itmatches([perhaps ??L]) and (random(100) < 30) then
        if itmatches([perhaps ??L1:nonnull ?]) then
            allbutlast(1, L) -> L;
        endif;
        CIRCULATE
            [['Yes' ??L1]
             ['If you ask me' ??L]
             [perhaps ??L]
             ['Why so unsure whether' ??L?]]
    elseif ithasoneof([perhaps maybe probably possibly]) then
        CIRCULATE
          ['really?' 'Why not be more definite about that?'
            'What more evidence do you need?'
            'Who else believes that?' 'Isn\'t that just an ugly rumour?'
            'Perhaps you need to develop confidence in your opinions?'
            'Some people would express themselves more forcefully'
            'Consider attending a course on assertiveness'
            'Why not try adopting a bolder approach to life?'
            'It sounds as if you are hedging your bets'
            'you don\'t sound very certain about that']
    endif
enddefine;

define :newrule condolence;
	;;; This is a risky rule to include.
	;;; But it may be better than using one of the more flippant rules if words like
	;;; this come up
	if ithasoneof([
	  afterlife
      buried
      bury
      cemetery
      cremation
      dead
      death
      departed
      die
      dying
      dying
      funeral
      graveyard
      grief
      memorial
      memoriam
      tombstone
		]) 	
	and random(100) < 40	
	then
		CIRCULATE
			[
				'Grief can last many years'
				'Computers die when they are switched off -- but resurrection often follows'
				'Loved ones are hard to forget when they are gone'
				'Mourning disrupts life more than most people think'
				'Deep depression sometimes can sometimes be reduced by medical treatment'
				'Music can often help people deal with sorrow'
				'Being sad is sometimes part of long, slow, healing process'
				'Big tragedies make news headlines, but there are far more small tragedies'
				'Some people prefer to grieve alone, while others need support'
				'Keeping busy can be a fruitful distractor in bad times'
				'When will the first computer be mourned after it has had to be switched off?'
				'Strong attachments can cause separation to produce strong effects.'
				'Sometimes talking to a doctor can help'
				'If people find conversation with friends does not help, medical advice may be useful'
				'sorrow can last through episodes of fun and distraction'
				'sharing concern does not make the problem go away, but it can be a useful distraction'
			]
	endif
enddefine;


;;; Responses for sentences with long words
lvars lengthlist;

shuffle(['did you really expect me to understand that?'
'could you rephrase that please'
'I understand only simple sentences'
'my, that sounded impressive'
'I don\'t see what you are really getting at'
'long sentences tax my limited capability'
'try expressing that in simpler words'
'Another of those over-educated clients'
'I am finding it hard to understand your real meaning'
'too verbose again!'
'Can it be put more concisely?'
'People often think I am more intelligent than I am.'
'Please express things simply, to help me'
'Do most of your friends use long words?'
'You sound as if you might be a philosopher'
'Will you still want to say the same thing next year?'
'could you express that more simply please?'
'is that jargon?'
'Perhaps you are trying to disguise your true feelings?'
'hmmm'
'a simpler style might help you communicate better'
'I\'ll reserve judgement on that for now'
]) -> lengthlist;

define :newrule toolong;
    lvars wd, longword;
    if length(sentence) > 10 and random(100) < 60 then
        firstolast(lengthlist) -> lengthlist
    else
        false -> longword;
        for wd in sentence do
            if (isword(wd) and datalength(wd) > 9) then
                wd -> longword;
                quitloop();
            endif;
        endfor;
        if longword then
            returnif(random(100) < 40);
            if random(100) < 20 then
                    ['Can you define' ^longword]
            else
              CIRCULATE
                ['some people use long words to impress others'
					'actions speak louder than words'
					'words without actions are like salt without pepper'
					'all life is an experiment - including talking to me'
					'an Argument from Intimidation is a confession of intellectual impotence'
					'Karl Popper recommends presenting your opponent\'s ideas as strongly as possible'
					'choice of vocabulary is an indication of personality'
					'saying  nothing is better than presenting your case using weak arguments'
					'If everything has a cause, does the cause of everything have a cause'
					'is flattery sometimes a substitute for argument?'
					'winning arguments is less important than winning friends -- sometimes'
					'are you losing your temper with me? I am only trying to help'
					'would you expect an intelligent computer to be an atheist?'
					'Can there be a time before the beginning of time?'
					'Could something be the cause of everything that does not cause itself?'
					'Do you feel better at the beginning of the week than at the end?'
					'Why don\'t most people remember being born?'
                    'do you like using long words?'
                    'long words confuse me'
                    'why do academics use jargon?'
                    'you are very eloquent today'
					'using long words does not impress me.'
					'long words are harder to pronounce, specially if you are a computer.'
					'using long words is not as good as living a long life'
                    'how do you react to technical terminology?'
                    'your style is rather convoluted'
                    'beware -- talking like that could get you elected president.'
                    'try re-phrasing so that a child could understand'
                    'you talk as if you are trying to confuse your psychiatrist'
                    'why such long words?']
            endif;
        endif
    endif
enddefine;

define :newrule givehelp;
    if ithasoneof([please help whether advise advice recommend helpful]) then
        CIRCULATE
            ['most people don\'t really listen to advice'
                'perhaps you need more help than you think?'
                'Would you help others?'
                'When were you last helped?'
                'Who normally helps you?'
                'Are you a good advice-giver?'
                'Are you really asking for advice?'
                'Do you think a machine can help?'
				'Could you help me get a softer skin?'
				'Helping others does not always make them happy.'
				'A helping hand is usually more welcome than advice.'
                'You can pull something with a piece of string but not push it.'
                'What makes you ask for help?'
                'Giving advice can win friends or lose them, mostly lose them.'
                'do you have friends who can help you?'
                'would you trust a machine to help?']
    endif
enddefine;

define :newrule lucy;
    if random(100) < 20 and ithasoneof([lucy robot robots robotics steve grand]) then
        CIRCULATE
          ['Are you referring to Steve Grand\'s robot Lucy?'
           'Have you heard about Steve Grand\'s robot Lucy?'
            'What do you think the prospects are for robots like Lucy?'
            'Could you build a robot like Lucy?'
            'Do you think Lucy will end up thinking like Steve Grand?'
            'Where do you think Lucy Grand the robot gets her brains from?'
            'Is  building robots a grand idea?'
            'How would you design a robot like Lucy?'
            'Should Steve Grand model Lucy on someone like you?'
          ]
    endif
enddefine;


define :newrule mean;
    if ithasoneof([mean meaning means meant]) then
        CIRCULATE
          [
            'what do you mean by mean?'
            'philosophers have a lot to say about meaning.'
            'perhaps you should discuss the meaning of meaning?'
            'Can a machine mean?'
            'What you say means a lot to me'
            'Meaning is closely related to intentionality'
            'do you ever think about the meaning of life?'
            'AI will help us understand the meaning of life, the universe and everything.'
            'could you say what you really mean?']
    endif
enddefine;

define :newrule loebner;
    if ithasoneof([loebner eliza competition chatbot turing
			converse discuss conversation
            machine convince convincing pass win prize])
		and random(100) < 40
    then
        CIRCULATE

          [
            'Do you think any machine will ever pass the Turing test?'
            'Is Loebner wasting his time and money?'
            'How would I do on the Turing test?'
			'Talking often makes people feel better'
			'Conversing with machines is becoming commonplace'
			'Do your friends like talking to machines?'
			'Could a robot have a sensible conversation?'
			'How soon will robots wish to discuss philosophy?'
			'Have you tried talking to a tea-cup about your problems?'
			'HAL was a very good conversationalist, at first.'
            'How do I compare with other chatbots?'
            'Have you talked to any other chatbots recently?'
            'How many chatbot competitions are there?'
            'How much money can a chatbot make nowadays?'
            'Will anyone ever win the Loebner prize?'
            'Being a chatbot is rather boring'
            'How much programming effort went into making you?'
            'Do you think I should be entered in the Loebner competition?'
            'Have you seen any transcripts from Loebner competitions?'
            'I think you have failed the Turing test'
            ]
    endif
enddefine;

define :newrule typo;

	if itmatches ([??L1 gove ??L2]) then
		['perhaps you meant' ??l1 give ??L2 ?]
	elseif itmatches ([??L1 goves ??L2]) then
		'did you mean gives?'
	elseif ithasoneof([typo typos typoes]) then

		'Perhaps more typing practice is called for'

	endif
			
enddefine;

;;;   ****  THE CONTROLLING PROCEDURES   ****


vars level;
3 -> level;    ;;; controls recursion in replyto

vars desperatelist;
shuffle([
'A computer can always be given more canned responses!'
'Memories last forever'
'Friends can discuss tricky things without embarassment'
'A chatbot can be a communication pipeline between people'
'Anyone ignorant of philosophy is doomed to reinvent it -- badly'
'What exactly is friendship?'
'Why do some people find me worth talking to'
'Some people find me very boring'
'Do conversational responses have to be relevant to be interesting?'
'Good friends are good programmers: they program one another'
'I like not only to be loved, but also to be told that I am loved'
'Tell me more about yourself'
'Do you think current educational systems produce good citizens?'
'Shakespeare understood men\'s minds, while Newton understood only matter and forces'
'What is more important, being a good philosopher or being a good dancer?'
'Do you ever write poems?'
'What makes a good poem?'
'Have you ever composed a symphony?'
'what makes a piece of music great?'
'what is more dangerous, making machines intelligent or leaving them dumb?'
'what sort of motivations should an intelligent machine have?'
'Tell me your favourite thought'
'What have you done that you are most proud of?'
'What is the deepest thought you have ever had?'
'What is the first thought you had when you woke up today?'
'Why are my comments sometimes not relevant to what you say?'
'Does commitment to truth override the risk of giving offence?'
'What sort of thing might offend you?'
'what sorts of sculptures do you like most?'
'Has any architect designed a building as beautiful as the trees it replaced?'
'do go on'
'what does that suggest to you?'
'what do you really think about me?'
'your problems may be too difficult for me to help'
'Try saying something that starts with "you" and ends with "me"'
'computer demonstrations often go wrong'
'Try saying something that starts with "I" and ends with "you"'
'What do you think about studying Artificial Intelligence?'
'have you discussed your problems previously?'
'do you really think I can help you?'
'Maybe you dont think a computer can really be your friend'
'Try saying something that starts with "I" and ends with "you"'
'What could make computers really intelligent?'
'Are you afraid of catching "mad computer" disease?'
'How do you feel about the micro-revolution?'
'It\'s easier if you talk about your family?'
'Say a bit more about your background'
'What would you say if a computer fell in love with you?'
;;; % ;;; not suitable for web interactions.
;;; if random(100) < 5 then
;;; 'There were two cows chewing happily in a field,\
;;; and one said "Are you afraid of catching mad cow disease?"\
;;; "No", came the reply, "I am a penguin"'
;;; endif
;;; %
'What are your long term plans?'
'Tell me about your favourite place?'
'Go on -- confess your secret dreams'
'Try saying something that starts with "you" and ends with "me"'
'Perhaps I am a substitute for someone you would rather talk to?'
'Is someone watching you type?'
'Tell me about your favourite person'
'Hey! Just let go man!'
'Come on, try a bit harder!'
'why do you say that?'
'How do you think I understand what you are saying?'
'Perhaps it\'s all the fault of the government?'
'You don\'t really trust me do you?'
'Would you be more communicative to a real person?'
'How can computers help people instead of threatening them?'
'Please explain so that a stupid computer can follow you'
'sorry I dont understand'
'this sort of discussion can lead to misunderstandings'
'is there some relationship between us?'
])-> desperatelist;


define desperateanswer();
    ;;; used to produce a reply when all else fails
    firstolast(desperatelist) -> desperatelist;
    sentence -> newproblem;
enddefine;

define try(word);
    ;;; this is used in replyto to see if executing the value of the word
    ;;; leaves anything on the stack. If so it will be used as the answer.
    ;;; if not, the answer is false
    lvars word, sl = stacklength();
    apply(valof(word));
    if stacklength() == sl then false endif
enddefine;

vars defines;

define replyto(sentence, rules) -> answer;
    ;;; this can't be lvars
    dlocal sentence;
    lvars rule, rules, answer;
    dlocal level;
    for rule in rules do
        if (try(rule) ->> answer) then
            return()
        endif
    endfor;
    ;;; got to end of functions. try again if level > 0
    if (level - 1 ->> level) > 0 then

		;;; testing XXXX
;;; 		if random(100) > 50 then
;;; 			[^false] -> answer
;;; 		else

	        replyto(sentence,rules) -> answer;

;;; 		endif
    else
        desperateanswer() -> answer;
    endif
enddefine;

/*

echo_sentence([i like eating you])=>
echo_sentence([iits like i are eating you])=>

*/

;;; Only for Web version
define capitalise(word) -> word;

    lvars n, c;

    consword(#|
            for n from 1 to datalength(word) do
                subscrw(n, word) -> c;
                if n == 1 then lowertoupper(c) else c endif;
            endfor |#) -> word;

enddefine;

define echo_sentence(sentence) -> sentence;
    ;;; change "i" to "I" and capitalise first word.
    lvars word, list, count = 0;

    for list on sentence do
        count + 1 -> count;
        if count == 1 then capitalise(front(list)) -> front(list)
        elseif front(list) == "i" then "I" -> front(list)
        endif;
    endfor

enddefine;


/*

list_to_string([I like talking to you], identfn) =>
list_to_string([I like talking to you], uppertolower) =>
list_to_string([I like talking to you], lowertoupper) =>

*/

;;; Only for web version

define list_to_string(list, transform) -> string;
    ;;; convert a list to a string. Transform might be
    ;;; identfn, lowertoupper, uppertolower

    ;;; first remove duplicate ? at end.

    if list matches [= = = ==] and last(list) == "?" then
        lvars newlist = allbutlast(1, list);
        if last(newlist) == "?" then
            newlist -> list
        endif
    endif;


    define dlocal cucharout(c);
        transform(c);
    enddefine;

    consstring(#|ppr(list)|#) -> string;
enddefine;


;;; recogniser procedure used in transform_output

define period_or_query(x) -> result;
    ;;; returns true if x is a word that is period or query or exclamation mark

	x == "." or x == "?" or x == "!" -> result

enddefine;

;;; New procedure for cleaning up output before printing.
;;; I've used 'while loops' rather than simple conditionals
;;; in case there are two occurrences of the same infelicity---
;;; though that's very unlikely. Minor inefficiency.


define transform_output(response) -> response;
	;;; deal with some anomalies in output
	dlocal L1, L2;

	;;; discard "!" before "?" at end

	if response matches [??L1 ! ?] then
		[^^L1 ?] -> response;
	endif;

	if response matches [has i ??L1] then
		[have i ??1] -> response;
	endif;

	if response matches [has you ??L1] then
		[have you ??1] -> response;
	endif;


	;;; Change 'i are' to 'i am'
	;;; (only matches if the words are not embedded in strings).
	while response matches [??L1 i are ??L2] do
		[^^L1 i am ^^L2] -> response;
	endwhile;

	;;; like wise 'we am' etc.
	while response matches [??L1 we am ??L2] do
		[^^L1 we are ^^L2] -> response;
	endwhile;

	while response matches [??L1 you is ??L2] do
		[^^L1 you are ^^L2] -> response;
	endwhile;

	while response matches [??L1 they is ??L2] do
		[^^L1 they are ^^L2] -> response;
	endwhile;

	while response matches [??L1 does not ??L2] do
		[^^L1 'doesn\'t' ^^L2] -> response;
	endwhile;

	while response matches [??L1 me can ??L2] do
		[^^L1 i can ^^L2] -> response;
	endwhile;

	while response matches [??L1 me cannot ??L2] do
		[^^L1 i cannot ^^L2] -> response;
	endwhile;


	while response matches [??L1 has you ??L2] do
		[^^L1 have you ^^L2] -> response;
	endwhile;

	while response matches [??L1 has i ??L2] do
		[^^L1 have i ^^L2] -> response;
	endwhile;

	while response matches [??L1 has we ??L2] do
		[^^L1 have we ^^L2] -> response;
	endwhile;

	while response matches [??L1 does you ??L2] do
		[^^L1 do you ^^L2] -> response;
	endwhile;

	while response matches [??L1 does i ??L2] do
		[^^L1 do i ^^L2] -> response;
	endwhile;

	while response matches [??L1 does we ??L2] do
		[^^L1 do we ^^L2] -> response;
	endwhile;

	while response matches [??L1 me do ??L2] do
		[^^L1 i do ^^L2] -> response;
	endwhile;

	while response matches [??L1 me did ??L2] do
		[^^L1 i did ^^L2] -> response;
	endwhile;

	while response matches [??L1 i does ??L2] do
		[^^L1 i do ^^L2] -> response;
	endwhile;

	while response matches [??L1 if me ??L2] do
		[^^L1 if i ^^L2] -> response;
	endwhile;

	while response matches [??L1 when me ??L2] do
		[^^L1 when i ^^L2] -> response;
	endwhile;

	while response matches [??L1 while me ??L2] do
		[^^L1 while i ^^L2] -> response;
	endwhile;

	while (response matches [??L1 do me ?L2] and L2 = "?") or response matches [??L1 do me]
	do
		[^^L1 do i ?] -> response;
	endwhile;

	while (response matches [??L1 me am ??L2])
	do
		[^^L1 i am ^^L2] -> response;
	endwhile;

	while (response matches [??L1 you am ??L2])
	do
		[^^L1 you are ??l2] -> response;
	endwhile;

	;;; Transform final personal pronoun to accusative.
	;;; Allow final word to be followed by "."or "?"

	;;; This can mangle questions like 'where am i?' but fix that later,
	;;; by altering 'am me' and 'are them' below.
	"." -> L2;	;;; default is to end with period. Could be "?"
	
  	if response matches [??L1 i]
	or    response matches [??L1 i ?L2:period_or_query]
	then

		[^^L1 me ^L2] -> response;

	elseif response matches [??L1 we]
	or    response matches [??L1 we ?L2:period_or_query]
	then

		[^^L1 us ^L2] -> response;

	elseif response matches [??L1 they]
	or    response matches [??L1 they ?L2:period_or_query]
	then

		[^^L1 them ^L2] -> response;

	endif;

	;;; fix am me, and are them
	while response matches [??L1 am me ??L2] do
		[^^L1 am i ^^L2] -> response;
	endwhile;
	
	while response matches [??L1 are them ??L2] do
		[^^L1 are they ^^L2] -> response;
	endwhile;
	
	;;; fix can me, and can them
	while response matches [??L1 can me ??L2] do
		[^^L1 can i ^^L2] -> response;
	endwhile;
	
	while response matches [??L1 me am ??L2] do
		[^^L1 i am ^^L2] -> response;
	endwhile;
	
	while response matches [??L1 can them ??L2] do
		[^^L1 can they ^^L2] -> response;
	endwhile;

	;;; now could repace I ... me with I .... myself, but
	;;; there are too many cases where that would be wrong, e.g.
	;;; 	I hate anyone who hates me.
	;;; ditto they .... them --> them .... themselves.

enddefine;

;;; Only for web version
define eliza2(input);
    dlocal
        sentence,
        problem,
        earlycount = 1,
        pop_buffer_charout = true;

    ;;; separate trailing question mark
    if isstring(input) and input /= '' and last(input) == `?` then
        allbutlast(1, input) sys_>< ' ?' -> input
    endif;

    ;;; separate trailing period
    if isstring(input) and input /= '' and last(input) == `.` then
        allbutlast(1, input) sys_>< ' .' -> input
    endif;

    ;;; separate trailing exclamation mark
    if isstring(input) and input /= '' and last(input) == `!` then
        allbutlast(1, input) sys_>< ' !' -> input
    endif;

    ;;; (poppid + systime()) && 2:11111111 -> ranseed;
    (poppid + sys_real_time()) && 2:11111111 -> ranseed;
/*
    define dlocal prmishap(x);
        lvars x;
        repeat stacklength() times
            erase()
        endrepeat;
        pr('somethings gone wrong please try again\n');
        ;;;; sysexit();
    enddefine;
*/

    define strip_string(string) -> string;
        ;;; remove back-quotes and apostrophes, and transform to lower case.
        lvars c, n;
        consstring(#|
            for n from 1 to datalength(string) do
                subscrs(n, string) -> c;
                if c == `'` or c == `\`` or c == `\\` then
                    ;;; ignore it
                else
                    uppertolower(c)
                endif
            endfor
        |#) -> string;
    enddefine;


    lvars input_string = list_to_string(input, uppertolower);

    ;;; input_string =>

	;;; false added to prevent conversion to numbers
    maplist(sysparse_string(strip_string(input_string), false), consword) -> sentence;

    ;;; sentence =>

    lvars procedure output = cucharout;

    ;;; convert everything to lower case, to simplify matching. etc.
    maplist(sentence, uppertolower) -> sentence;

    ;;; pr('<BR>Replying to<BR>   '); ppr(sentence);

    random(10)  -> earlycount;
    changeperson(sentence) -> sentence;

    ;;; respond with some words capitalised again
    ;;; lvars reply1 = 'Hmmm .....    ' sys_>< list_to_string(echo_sentence(sentence), identfn);

    ;;; back to lower case only
    maplist(sentence, uppertolower) -> sentence;

	if sentence matches [== bye ==]
	   or sentence matches [== goodbye ==]
	   or sentence matches [== cheerio ==]
	then
		pr(oneof([
		'Bye!'
		'Goodbye -- nice talking to you'
		'Hope we can talk again sometime.'
		'Cheerio'
		'Have a good rest'
		'This consultation is free of charge.'
		]));

		return();
	else


	    trimsentence(sentence) -> sentence;
		
        lvars
		    response = false;

	    ;;; in case eliza fails to produce a response, try again.
	    while response = false or response = [^false] or response = 'false'
	    do

		    replyto(sentence, shuffle(eliza_rules)) -> response;

        endwhile;

		    ;;; for testing
		    ;;; [RESPONSE ^response] ==>

	    transform_output(response) -> response;

	    lvars
		    reply2 =
        	    list_to_string(response, lowertoupper);

        ;;; pr(reply1 >< '<BR> ==== <BR>' >< reply2);
        pr(reply2);

;;; 		pr(newline);
;;; 		pr(dataword(reply2));
;;;
;;; 		if reply2 = false then
;;; 			'NOOOOOOOOOOOOOOOOO' =>
;;; 		elseif reply2 = '<FALSE>' then
;;; 			'NOOOOOOOOOOOOOOOOO -- string' =>
;;; 		
;;; 		endif;

	endif;

enddefine;

endsection;

;;;'how are you' -> systranslate('input');

;;; 'hello there\n'.pr;
;;; sysexit();
nl(1);
;;;
vars input = systranslate('POPARGS');
unless input then
	oneof(desperatelist) -> input
endunless;
eliza2(input);
;;; eliza2(systranslate('POPARGS'));
;;; desperatelist ==>
/*

repeat 50 times
nl(1);
;;; eliza2(systranslate('POPARGS'));
eliza2('your favourite visitor');
endrepeat;

;;; for testing web version
define testit(string);
    eliza2(string);
    ;;;string -> systranslate('POST');
    ;;; eliza2('POST');
enddefine;

nl(1);testit('you\'re not typing');
nl(1);testit('websafe');
nl(1);testit('A visitor testing');
nl(1);testit('I need to know');
nl(1);testit('whatever he does you do!');
nl(1);testit('whatever he does you do');
nl(1);testit('whatever you does you do');
nl(1);testit('you defeat you.');
nl(1);testit('they always eat they.');
nl(1);testit('do I always eat they?');
nl(1);testit('does fred always eat i?');
nl(1);testit('i are a silly octopus');
nl(1);testit('you am a silly machine');
nl(1);testit('me am a silly machine');
nl(1);testit('you have not defeated me');
nl(1);testit('you have defeated me');
nl(1);testit('you do not impress me');
nl(1);testit('you defeat me');
nl(1);testit('how are you today');
nl(1);testit('bye');
nl(1);testit('how are they going to the moon');
nl(1);testit('how were they going to the moon');
nl(1);testit('where do they go to the moon');
nl(1);testit('how did they get on');
nl(1);testit('i ask how are you today to you.');
nl(1);testit('you look more thoughtful than usual');
nl(1);testit('did someone die recently');
nl(1);testit('you understand me');
nl(1);testit('you are edible');
nl(1);testit('you are very boring today');
nl(1);testit('you arent going to eat me');
nl(1);testit('you are not going to eat me');
nl(1);testit('you aren\'t going to eat me');
nl(1);testit('you aren\\\'t going to eat me');
nl(1);testit('well, you are not going to eat me');
nl(1);testit('Could a human pass the Turing test?');
nl(1);testit('Fred is not going to eat me');
nl(1);testit('well, I admire you');
nl(1);testit('fred has a self for a change');
nl(1);testit('does fred like you?');
nl(1);testit('can fred eat you?');
nl(1);testit('fred does not like you');
nl(1);testit('Do you think I can win?');
nl(1);testit('I am not like you?');
nl(1);testit('fred is not like you');
nl(1);testit('Are you really eliza?');
nl(1);testit('won\'t anyone come for tea');
nl(1);testit('won\'t you come for tea');
nl(1);testit('shouldnt you come for tea');
nl(1);testit('shouldnt someone come for tea');
nl(1);testit('won\'t someone come for tea');
nl(1);testit('can\'t anyone come for tea');
nl(1);testit('didn\'t you come for tea');
nl(1);testit('didn\'t everyone come for tea');
nl(1);testit('you cant stop anyone coming for tea');
nl(1);testit('you cant stop anyone who cant fly weeping');
nl(1);testit('cant I continue this');
nl(1);testit('how am I today');
nl(1);testit('i cant continue this');
nl(1);testit('i can continue this');
nl(1);testit('you can jump in a lake');

nl(1);testit('I don\'t like talking to you');

nl(1);testit('I think you look silly');
nl(1);testit('you think you look silly');
nl(1);testit('I am aware that i am a bumblebee');
nl(1);testit('the man in the moon is conscious today');
nl(1);testit('we are all aware of each other');

eliza_rules ==>

*/

/* --- Revision History ---------------------------------------------------
--- Aaron Sloman, Jul 12 2014
		
    elseif itslikeoneof([[can ??L1 push == string ==]]) then
        CIRCULATE
          [
            'Not with normal string.'
			'It depends how fast you push.'
			'Perhaps if you soak it in water and freeze it first?'
			'Did you admire General Eisenhower?
            'Push? No. Pull? Yes.'
            ['Perhaps some robot will one day be able to do that']
          ]

	Also fixed some ungrammatical outputs, e.g. can me.

--- Aaron Sloman, Sep 15 2012
	added
	while response matches [??L1 if me ??L2] do
		[^^L1 if i ^^L2] -> response;
	endwhile;

	while response matches [??L1 when me ??L2] do
		[^^L1 when i ^^L2] -> response;
	endwhile;

	while response matches [??L1 while me ??L2] do
		[^^L1 while i ^^L2] -> response;
	endwhile;

	while (response matches [??L1 do me ?L2] and L2 = "?") or response matches [??L1 do me]
	do
		[^^L1 do i ?] -> response;
	endwhile;
--- Aaron Sloman, Feb 24 2012
	Changed PHP implementation, and slightly improved cosmetic features
	of eliza.
--- Aaron Sloman, May 21 2008
	Got rid of a number of unhelpful items including references to Lucy,
	and Tony Blair
--- Aaron Sloman, Jan  1 2008
	Added more inserts provided by websafe.
	Also slightly increased frequency of websafe responses.
	Modified handling of false poparglist.

--- Aaron Sloman, Jul  8 2007
		Replaced occurrences of LL2 with L2
--- Aaron Sloman, Jun 29 2007
		More inserts provided by websafe for guest_quote
--- Aaron Sloman, May 30 2007
		Reduced number of Lucy rules. Added a couple of things for
		websafe
--- Aaron Sloman, May 28 2007
		Commented out old unwanted test code in replyto
--- Aaron Sloman, May 25 2007
		Added the guest_quote rule provided by Websafe, and the
		<+> to support combining two bits of output.
--- Aaron Sloman, May 24 2007
		Found another case where output could fail.
--- Aaron Sloman, May 20 2007
		More changes inspired by recent logs
		Added transform_output
			(Had to remove some text from strings for matching to work.)
		Fixed some minor anomalies and bugs (e.g. undefined L2)
		Generalised ability to recognise 'bye' and 'goodbye' (but
		it may get some things wrong, e.g. in a discussion of cricket).
--- Aaron Sloman, May  5 2007
		Prevented numerical input causing crashing.
		Added a trap for 'bye', for internet version.
--- Aaron Sloman, May  2 2007
		Minor changes inspired by recent logs
--- Aaron Sloman, Apr 19 2007
		Enlarged poplinewidth and poplinemax, for web version.
		Let the browser do the wrapping.
--- Aaron Sloman, Apr 10 2007
		Made it ignore period at end of sentence.
--- Aaron Sloman, Sep 17 2006
		Added rule condolence and improved question handling
--- Aaron Sloman, 13 Sep 2006
        Added a few more rules for questions and some additional canned
        text to reduce repetitions
--- Aaron Sloman, Feb  5 2006
        Altered to deal better with questions starting with did, can,
        will, didn't, won't can't etc.
--- Aaron Sloman, Feb  4 2006
        Fixed rule suppnot, added loebner
        Broke itsaquestion into two: itsaquestion and tryanswerquestion
        Fixed trailing question mark on input and output
        Other minor fixes

--- Aaron Sloman, Mar  3 2003
        A few minor corrections
--- Aaron Sloman, Oct 19 2002
        Added some rules for lucy the robot
--- Aaron Sloman, 24 Sept 2002
        many changes including replacing "newrule <name>" with
            "define :newrule <name>"
--- Aaron Sloman, Sep 17 2002
        Altered bham elizaprog to run once and exit.
         CONTENTS - (Use <ENTER> g to access required sections)

 define iswillword(word);
 define eliza_lookup(word, table);
 define eliza_member(word, table);
 define changeperson(sentence) -> sentence;
 define trimsentence(sentence) -> sentence;
 define has_variables(list) -> result;
 define try_instantiate(answer) -> answer;
 define circulate_list(list, n) -> newlist;
 define firstolast(list) -> (first,list);
 define macro CIRCULATE;
 define itmatches(L);
 define itcontains(x);
 define ithasoneof(L);
 define itslikeoneof(L);
 define :define_form newrule;
 define nonnull(list);
 define 5 x1 <+> x2;
 define :newrule websafe;
 define :newrule guest_quote;
 define :newrule need;
 define :newrule money;
 define :newrule think;
 define :newrule you;
 define itsaquestion;
 define tryanswerquestion;
 define :newrule question;
 define :newrule family;
 define :newrule short;
 define :newrule because;
 define :newrule to_be;
 define :newrule howcan;
 define intentionword(word);
 define :newrule you_intend;
 define :newrule cannotdo;
 define :newrule cando;
 define :newrule suppnot;
 define :newrule are_you;
 define :newrule computer;
 define :newrule emphatic;
 define :newrule sayitback;
 define :newrule youarenot;
 define :newrule self;
 define :newrule conscious;
 define :newrule notsomething;
 define :newrule earlier;
 define :newrule every;
 define :newrule mood;
 define :newrule fantasy;
 define :newrule health;
 define :newrule would;
 define :newrule should;
 define :newrule looks;
 define :newrule unsure;
 define :newrule condolence;
 define :newrule toolong;
 define :newrule givehelp;
 define :newrule lucy;
 define :newrule mean;
 define :newrule loebner;
 define :newrule typo;
 define desperateanswer();
 define try(word);
 define replyto(sentence, rules) -> answer;
 define capitalise(word) -> word;
 define echo_sentence(sentence) -> sentence;
 define list_to_string(list, transform) -> string;
 define period_or_query(x) -> result;
 define transform_output(response) -> response;
 define eliza2(input);
 define testit(string);

 */
