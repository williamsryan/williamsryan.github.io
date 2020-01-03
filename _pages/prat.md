---
layout: posts
permalink: /projects/prat/
---

## Program Representation and Analysis Toolkit (PRAT)

TODO: Writeup about this project/publication later.

```perl
sub make_ifdef_processor {
   my $map_symbols = shift;

   return sub {
      my $fn = $_;

      if ( $fn =~ /svn-base/ ) {
         return;
      }

      open FILE, "<$fn" or die "Error opening file $fn ($!)";
      while ( my $line = <FILE> ) {
         if ( $line =~ /^\/\// ) { # skip C-style comments.
            next;
         }

         if ( $line =~ /#ifdef\s+(.*)$/ ) {
            print "matched line in $fn $line";
            my $symbol = $1;
            push @{ $map_symbols->{$fn} }, $symbol;
         }
      }
   }
}

__END__
```
