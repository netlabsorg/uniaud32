/* rexx */
parse arg Rev1 Rev2;

address CMD 'git diff -x -w -r '||Rev1||':'||Rev2||' >'||Rev1||'-'||Rev2||'.diff';
