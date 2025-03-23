\chapter*{Introduction}
\addcontentsline{toc}{chapter}{Introduction}

These are the notes for the course on type systems for programming languages given at Eötvös Loránd University (Autumn semesters 2020--2023, Computer Science MSc course). Previous versions of this course used Robert Harper's book \cite{harper} (Autumns 2016--2019) and István Csörnyei's books \cite{csornyei,csornyeiLambda} (before 2016). Other excellent textbooks on the topic are \cite{pierce,Pierce:SF2,plfa20.07}.

In these notes we define programming languages as algebraic theories (see Chapter \ref{ch:precision} and \cite{godelTalk}). Most of the material is formalised in Agda, it uses an equality type in strict Prop \cite{DBLP:journals/pacmpl/GilbertCST19} with a postulated strong tranport rule and postulated quotient inductive-inductive types \cite{popl19}. Their computation rules are added to Agda using rewrite rules \cite{cockxsprinkles}.

These notes are compiled from literate Agda files and are available at \url{https://bitbucket.org/akaposi/typesystems}. They are under continuous development.

Special thanks to Bálint Kocsis and Márk Széles who developed the first version of the formalisation during a summer internship in 2020. Thanks to István Donkó, Viktor Bense and Szumi Xie who developed materials for the tutorials and contributed significantly to the formalisation. Thanks to the following students who fixed errors and typos: Dávid Gábor, András Kovács, Kálmán Kostenszky, Álmos Sőnfeld, Erik Sulcz, András Vadász, Barnabás Zahorán. Thanks to the students of the course for their excellent questions.
