library(tidyverse)
dev_tbl <- read_csv("summary_dev.csv", skip = 4) %>%
    rename(`develop time(s)` = 'time(s)')

tc_tbl <- read_csv("summary_typeclasses.csv", skip = 4) %>%
    rename(`typeclass time(s)` = 'time(s)')

combined_tbl <- full_join(dev_tbl, tc_tbl) %>%
    mutate(`typeclass - develop time(s)` = `typeclass time(s)` - `develop time(s)`) %>%
    arrange(desc(`typeclass - develop time(s)`)) %>%
    mutate(result=NULL)

write_csv(combined_tbl, "compare-typeclass.csv")
