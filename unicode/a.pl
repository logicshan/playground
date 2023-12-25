#!/usr/bin/perl
use utf8;      # so literals and identifiers can be in UTF-8
use v5.12;     # or later to get "unicode_strings" feature
use strict;    # quote strings, declare variables
use warnings;  # on by default
use warnings  qw(FATAL utf8);    # fatalize encoding glitches
use open      qw(:std :encoding(UTF-8)); # undeclared streams in UTF-8
use charnames qw(:full :short);  # unneeded in v5.16

my $s =  "नमस्ते";
my @a = $s =~ /(\X)/g;
print "$s\n";
print join(" ", @a), "\n";

my $str = join("", reverse $s =~ /\X/g);
@a = $str =~ /(\X)/g;
print "$str\n";
print join(" ", @a), "\n";