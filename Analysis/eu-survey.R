######---Load libraries---######

library(tidyverse)
library(ggdist)
library(survival)
library(ranger)
library(ggfortify)
library(modelsummary)
library(rstatix)
library(monochromeR)
#library(dlookr)
library(epitools)
library(ggsurvfit)
library(broom)
library(DescTools)
library(rstan)
library(brms)
library(confintr)
library(gtsummary)
library(quantreg)
library(patchwork)
library(ggridges)
library(tidymodels)
#library(ggpattern)
library(rworldmap)
library(tinytable)
library(gt)
library(epiR)
library(readxl)
#library(brms)
library(scales)
library(marginaleffects)
library(ggthemes)
library(emmeans)
library(easystats)
# options(brms.backend = "cmdstanr")


######---Define functions---######


convert_prop <- function(x) {
  # Ensure that the input is a numeric vector
  if (!is.numeric(x)) {
    stop("Input must be a numeric vector.")
  }
  
  # Calculate the minimum and maximum values
  min_value <- min(x, na.rm = TRUE)  # Use na.rm = TRUE to handle NA values
  max_value <- max(x, na.rm = TRUE)
  
  # Handle the case where all values are identical
  if (min_value == max_value) {
    warning("All values in the vector are the same. Returning a vector of zeros.")
    return(rep(0, length(x)))
  }
  
  # Apply the min-max scaling transformation
  scaled_x <- (x - min_value) / (max_value - min_value)
  
  return(scaled_x)
}


collect_model_results <- function(df, outcome_var) {
  predictors <- setdiff(names(df), outcome_var)
  
  results <- lapply(predictors, function(predictor) {
    # Clean the predictor name by replacing "-" with "_"
    clean_predictor <- gsub("-", "_", predictor)
    
    # Clean the column name in the dataframe
    colnames(df)[colnames(df) == predictor] <- clean_predictor
    
    # Create the formula with the cleaned predictor name
    formula <- as.formula(paste(outcome_var, "~", clean_predictor))
    
    # Fit the linear model
    model <- lm(formula, data = df)
    
    # Extract model summary statistics
    model_summary <- broom::glance(model) %>%
      dplyr::mutate(predictor = clean_predictor)
    
    # Extract coefficient details, excluding the intercept
    coef_details <- broom::tidy(model, conf.int = TRUE) %>%
      dplyr::filter(term != "(Intercept)") %>%
      dplyr::mutate(predictor = clean_predictor)
    
    # Ensure that the required columns exist in coef_details
    if (all(c("conf.low", "conf.high") %in% names(coef_details))) {
      coef_details <- coef_details %>%
        dplyr::select(predictor, term, estimate, std.error, statistic, p.value, conf.low, conf.high)
    } else {
      coef_details <- coef_details %>%
        dplyr::select(predictor, term, estimate, std.error, statistic, p.value) %>%
        dplyr::mutate(conf.low = NA, conf.high = NA)
    }
    
    # Combine model summary and coefficient details into one tibble
    result <- coef_details %>%
      dplyr::bind_cols(model_summary %>%
                         dplyr::select(r.squared, adj.r.squared, sigma, statistic = statistic, p.value = p.value, df, logLik, AIC, BIC, deviance, df.residual, nobs) %>%
                         dplyr::rename(
                           model_r_squared = r.squared,
                           model_adj_r_squared = adj.r.squared,
                           model_sigma = sigma,
                           model_statistic = statistic,
                           model_p_value = p.value,
                           model_df = df,
                           model_logLik = logLik,
                           model_AIC = AIC,
                           model_BIC = BIC,
                           model_deviance = deviance,
                           model_df_residual = df.residual,
                           model_nobs = nobs
                         ))
    
    return(result)
  })
  
  # Combine results into a single tibble
  results_df <- dplyr::bind_rows(results)
  return(results_df)
}



mutate_round <- function(data, digits = 2) {
  data %>%
    mutate(across(where(is.numeric), ~ round(., digits)))
}

univariate_predictors <- function(df, outcome_var) {
  # Ensure outcome_var is not included in the predictors
  predictors <- setdiff(names(df), outcome_var)
  
  # Check for predictors that are not present in the dataframe
  missing_predictors <- setdiff(predictors, names(df))
  if (length(missing_predictors) > 0) {
    stop(
      "These predictors are not in the dataframe: ",
      paste(missing_predictors, collapse = ", ")
    )
  }
  
  results <- lapply(predictors, function(predictor) {
    # Ensure predictor exists in df
    if (!predictor %in% names(df)) {
      stop(paste("Predictor", predictor, "not found in dataframe"))
    }
    
    # Convert binary numeric predictors to factors
    if (is.numeric(df[[predictor]]) &&
        all(df[[predictor]] %in% c(0, 1))) {
      df[[predictor]] <- as.factor(df[[predictor]])
    }
    
    # Fit the linear model
    formula <- as.formula(paste(outcome_var, "~", predictor))
    model <- lm(formula, data = df)
    
    # Get model glance
    model_glance <- broom::glance(model)
    
    # Extract relevant statistics from glance output
    r_squared <- model_glance$r.squared
    adj_r_squared <- model_glance$adj.r.squared
    sigma <- model_glance$sigma
    statistic <- model_glance$statistic
    p_lm_value <- model_glance$p.value
    df_model <- model_glance$df
    logLik <- model_glance$logLik
    AIC <- model_glance$AIC
    BIC <- model_glance$BIC
    deviance <- model_glance$deviance
    
    # Determine if predictor is categorical or continuous
    predictor_is_categorical <- is.factor(df[[predictor]]) ||
      is.character(df[[predictor]])
    
    # Calculate margins
    if (predictor_is_categorical) {
      margins <- marginaleffects::avg_predictions(model, by = predictor)
      margins_tidy <- as_tibble(margins) %>%
        dplyr::mutate(term = as.character(.data[[predictor]]))  # Ensure 'term' is set
    } else {
      # Calculate mean and standard deviation of the predictor
      mean_value <- mean(df[[predictor]], na.rm = TRUE)
      sd_value <- sd(df[[predictor]], na.rm = TRUE)
      
      # Create a data grid with mean, mean - sd, and mean + sd
      datagrid <- data.frame(
        value = c(mean_value - sd_value, mean_value, mean_value + sd_value),
        label = c("mean - sd", "mean", "mean + sd")
      )
      
      # Rename the column to match the model's predictor name
      colnames(datagrid)[1] <- predictor
      
      # Compute predictions
      pred <- marginaleffects::predictions(model, newdata = datagrid)
      pred$term <- datagrid$label  # Ensure 'term' is set
      
      # Convert predictions to a tibble
      margins_tidy <- as_tibble(pred)
    }
    
    # Handle categorical predictors
    if (predictor_is_categorical) {
      # Make sure term is correctly represented for categorical
      margins_tidy <- margins_tidy %>%
        dplyr::mutate(term = factor(term, levels = unique(.data[[predictor]])))
    } else {
      # For continuous predictors, the term is already set
      margins_tidy <- margins_tidy %>%
        dplyr::mutate(term = factor(term, levels = c("mean - sd", "mean", "mean + sd")))
    }
    
    # Ensure that 'predictor' column is included correctly
    margins_tidy <- margins_tidy %>%
      dplyr::mutate(predictor = predictor)
    
    # Select and reorder columns
    margins_tidy <- margins_tidy %>%
      dplyr::select(predictor,
                    term,
                    estimate,
                    std.error,
                    statistic,
                    p.value,
                    conf.low,
                    conf.high)
    
    # Add model statistics to margins tidy results
    margins_tidy <- margins_tidy %>%
      dplyr::mutate(
        r_squared = r_squared,
        adj_r_squared = adj_r_squared,
        sigma = sigma,
        statistic = statistic,
        p_lm_value = p_lm_value,
        df = df_model,
        logLik = logLik,
        AIC = AIC,
        BIC = BIC,
        deviance = deviance
      )
    
    # Return margins tidy results
    margins_tidy
  })
  
  # Combine results into a tibble
  results_df <- dplyr::bind_rows(results)
  
  return(results_df)
}



multiemmeans <- function(data, outcome_var) {
  # Identify binary variables (excluding the outcome variable)
  binary_vars <- colnames(data)[sapply(data, function(x)
    all(x %in% c(0, 1))) & colnames(data) != outcome_var]
  
  # Function to perform ANOVA and collect results
  get_anova_results <- function(var) {
    # Fit ANOVA model
    model <- aov(as.formula(paste(outcome_var, "~", var)), data = data)
    
    # Get ANOVA summary
    anova_summary <- summary(model)
    
    # Get EMMEANS
    emm <- tryCatch(
      emmeans::emmeans(model, specs = var),
      error = function(e)
        tibble()  # Return an empty tibble if error occurs
    )
    
    # Convert EMMEANS to a tibble and rename the grouping variable to 'group'
    emm_tibble <- as_tibble(emm) %>%
      rename(group = all_of(var))
    
    # Check if 'group' column is correctly renamed
    if (!"group" %in% colnames(emm_tibble)) {
      stop(paste("Grouping column not found in EMMEANS for variable:", var))
    }
    
    # Create a tibble with the results
    tibble(
      variable = var,
      p_value = anova_summary[[1]][["Pr(>F)"]][1],
      # p-value of the factor
      emmeans = list(emm_tibble)
    )
  }
  
  # Apply the function to each binary variable and combine results
  results <- map_dfr(binary_vars, get_anova_results)
  
  # Expand and format the results
  results_expanded <- results %>%
    unnest(emmeans) %>%
    dplyr::select(variable, p_value, group, emmean, SE, df, lower.CL, upper.CL)
  
  return(results_expanded)
}


col_n_sum <- function(df, ...) {
  # Collect column arguments into a list
  columns <- list(...)
  
  # Retrieve column names from indices or use names directly
  column_names <- sapply(columns, function(col) {
    if (is.numeric(col)) {
      name <- names(df)[col]
      if (is.na(name)) {
        stop("Column index is out of range.")
      }
    } else {
      name <- col
    }
    
    if (!(name %in% names(df))) {
      stop("The specified column does not exist in the data frame.")
    }
    
    return(name)
  })
  
  # Count occurrences of each unique combination of specified columns
  df %>%
    count(across(all_of(column_names))) %>%
    mutate(sum = sum(n)) # Add a column with the sum of counts
}



pci <- function(x, n, conf.level = 0.95) {
  xnc <- cbind(x, n, conf.level)
  lower <- numeric(nrow(xnc))
  upper <- numeric(nrow(xnc))
  for (i in 1:nrow(xnc)) {
    ci <- binom.test(x = xnc[i, 1],
                     n = xnc[i, 2],
                     conf.level = xnc[i, 3])$conf.int
    lower[i] <- ci[1]
    upper[i] <- ci[2]
  }
  dplyr::tibble(
    x = x,
    n = n,
    proportion = x / n,
    lower = lower,
    upper = upper,
    conf.level = conf.level
  )
}

pcit <- function(data, conf.level = 0.95) {
  # Identify numeric columns
  numeric_cols <- sapply(data, is.numeric)
  
  # Ensure there are at least two numeric columns
  if (sum(numeric_cols) < 2) {
    stop("The dataset must contain at least two numeric columns.")
  }
  
  # Get indices of the first and second numeric columns
  numeric_col_indices <- which(numeric_cols)
  
  if (length(numeric_col_indices) < 2) {
    stop("Not enough numeric columns found.")
  }
  
  # Extract the first and second numeric columns
  x <- data[[numeric_col_indices[1]]]
  n <- data[[numeric_col_indices[2]]]
  
  # Ensure that n >= x for all cases
  if (any(n < x)) {
    stop("Each trial count must be greater than or equal to the success count.")
  }
  
  # Initialize vectors for confidence intervals
  lower <- numeric(nrow(data))
  upper <- numeric(nrow(data))
  
  # Calculate confidence intervals for each row
  for (i in seq_len(nrow(data))) {
    ci <- binom.test(x = x[i],
                     n = n[i],
                     conf.level = conf.level)$conf.int
    lower[i] <- ci[1]
    upper[i] <- ci[2]
  }
  
  # Identify non-numeric columns for grouping
  non_numeric_cols <- names(data)[!numeric_cols]
  
  # Create a tibble including all original columns and calculated results
  result <- tibble(
    # Include non-numeric columns
    data[, non_numeric_cols, drop = FALSE],
    
    # Calculated columns with distinct names
    successes = x,
    trials = n,
    proportion = x / n,
    lower = lower,
    upper = upper,
    conf.level = conf.level
  )
  
  return(result)
}


to_dummmy <- function(df) {
  # Identify columns that are factors or characters with three or more unique levels
  multi_level_vars <- df %>%
    dplyr::select(where(~ (is.factor(.) || is.character(.)) && n_distinct(.) >= 3)) %>%
    names()
  
  # Separate the rest of the data
  df_other <- df %>%
    dplyr::select(-all_of(multi_level_vars))
  
  # Initialize a list to store dummy data frames
  dummy_dfs <- list()
  
  # Iterate over each selected variable to create dummy variables
  for (var in multi_level_vars) {
    # Ensure that NAs are handled properly by converting them to a separate category
    df[[var]] <- as.factor(df[[var]])
    df[[var]] <- addNA(df[[var]], ifany = TRUE)
    
    # Create dummy variables using model.matrix
    dummies <- model.matrix(~ df[[var]] - 1) %>%
      as.data.frame() %>%
      rename_with(~ paste0(var, "_", gsub("[^[:alnum:]_]", "_", .)))
    
    # Add the dummy variables to the list
    dummy_dfs[[var]] <- dummies
  }
  
  # Combine original data with dummy data frames
  result <- bind_cols(df_other, bind_cols(dummy_dfs))
  
  # Return the modified data frame as a tibble
  return(as_tibble(result))
}



compare_proportions <- function(data,
                                conf.level = 0.95,
                                method = "holm") {
  # Validate the input data
  required_cols <- c("proportion", "trials")
  if (!all(required_cols %in% names(data))) {
    stop("The input data must contain 'proportion' and 'trials' columns.")
  }
  # Identify group columns dynamically (assuming non-numeric columns are groups)
  non_numeric_cols <- names(data)[!sapply(data, is.numeric)]
  if (length(non_numeric_cols) == 0) {
    stop("No non-numeric columns found for grouping.")
  }
  # Get all combinations of non-numeric columns for group identification
  group_cols <- non_numeric_cols
  # Ensure there are at least two groups to compare
  if (nrow(data) < 2) {
    stop("The dataset must contain at least two groups for comparison.")
  }
  # Create a grid of pairwise combinations of the groups
  combinations <- combn(seq_len(nrow(data)), 2, simplify = FALSE)
  # Function to calculate differences, p-values, and confidence intervals for each pair
  calculate_difference <- function(index_pair) {
    i <- index_pair[1]
    j <- index_pair[2]
    
    group1 <- data[i, ]
    group2 <- data[j, ]
    
    # Proportion difference
    prop_diff <- group1$proportion - group2$proportion
    # Standard error for the difference in proportions
    pooled_se <- sqrt(
      group1$proportion * (1 - group1$proportion) / group1$trials +
        group2$proportion * (1 - group2$proportion) / group2$trials
    )
    
    small_constant <- 1e-10
    pooled_se <- max(pooled_se, small_constant)
    
    # Prevent division by zero
    if (pooled_se == 0) {
      stop("Standard error is zero; cannot compute z-score and p-value.")
    }
    z_score <- prop_diff / pooled_se
    # Calculate p-value for the proportion difference
    p_value <- 2 * (1 - pnorm(abs(z_score)))
    # Calculate confidence interval for the proportion difference
    z_critical <- qnorm(1 - (1 - conf.level) / 2)
    ci_lower <- prop_diff - z_critical * pooled_se
    ci_upper <- prop_diff + z_critical * pooled_se
    
    result <- tibble(
      # Add group identifiers dynamically
      !!!setNames(
        lapply(group_cols, function(col) group1[[col]]),
        paste0("gr1_", group_cols)
      ),
      !!!setNames(
        lapply(group_cols, function(col) group2[[col]]),
        paste0("gr2_", group_cols)
      ),
      prop_diff = prop_diff,
      z_score = z_score,
      p_value = p_value,
      ci_lower = ci_lower,
      ci_upper = ci_upper
    )
    
    return(result)
  }
  
  # Apply the calculate_difference function to each pair
  results <- map_dfr(combinations, calculate_difference)
  
  # Adjust p-values for multiple comparisons
  results <- results %>%
    mutate(adj_p_value = p.adjust(p_value, method = method))
  
  return(results)
  }

# Define the compare_proportions_by function for direct comparisons
compare_proportions_by <- function(data,
                                   conf.level = 0.95,
                                   method = "holm") {
  # Validate the input data
  required_cols <- c("proportion", "trials")
  if (!all(required_cols %in% names(data))) {
    stop("The input data must contain 'proportion' and 'trials' columns.")
  }
  
  # Automatically determine group and subgroup variables
  group_var <- names(data)[1]
  subgroup_var <- names(data)[2]
  
  # Split the data by group
  grouped_data <- split(data, data[[group_var]])
  
  # Function to calculate differences, p-values, and confidence intervals for each subgroup
  calculate_difference_within_group <- function(df) {
    # Generate pairwise comparisons for subgroups
    pairwise_comparisons <- combn(unique(df[[subgroup_var]]), 2, simplify = FALSE)
    
    # Initialize an empty result dataframe
    result_list <- list()
    
    for (pair in pairwise_comparisons) {
      subgroup1 <- df %>% filter(!!sym(subgroup_var) == pair[1])
      subgroup2 <- df %>% filter(!!sym(subgroup_var) == pair[2])
      
      # Ensure there is exactly one row in each subgroup
      if (nrow(subgroup1) != 1 || nrow(subgroup2) != 1) {
        warning("Each subgroup should have exactly one entry for comparison.")
        next
      }
      
      # Calculate proportion difference
      prop_diff <- subgroup1$proportion - subgroup2$proportion
      
      # Standard error for the difference in proportions
      pooled_se <- sqrt(
        subgroup1$proportion * (1 - subgroup1$proportion) / subgroup1$trials +
          subgroup2$proportion * (1 - subgroup2$proportion) / subgroup2$trials
      )
      small_constant <- 1e-10
      pooled_se <- max(pooled_se, small_constant)
      # Prevent division by zero
      if (pooled_se == 0) {
        warning("Standard error is zero; cannot compute z-score and p-value.")
        next
      }
      
      z_score <- prop_diff / pooled_se
      
      # Calculate p-value for the proportion difference
      p_value <- 2 * (1 - pnorm(abs(z_score)))
      
      # Calculate confidence interval for the proportion difference
      z_critical <- qnorm(1 - (1 - conf.level) / 2)
      ci_lower <- prop_diff - z_critical * pooled_se
      ci_upper <- prop_diff + z_critical * pooled_se
      
      # Append the results for this pairwise comparison
      result_list[[length(result_list) + 1]] <- tibble(
        group = unique(df[[group_var]]),
        subgroup1 = pair[1],
        subgroup2 = pair[2],
        prop_diff = prop_diff,
        z_score = z_score,
        p_value = as.numeric(p_value),
        # Ensure p_value is numeric
        ci_lower = ci_lower,
        ci_upper = ci_upper
      )
    }
    
    # Combine all results into one dataframe
    bind_rows(result_list)
  }
  
  # Apply the calculation function to each group
  results <- map_dfr(grouped_data, calculate_difference_within_group)
  
  # Adjust p-values for multiple comparisons if p_value column is correctly numeric
  if (nrow(results) > 0) {
    results <- results %>%
      mutate(adj_p_value = p.adjust(p_value, method = method)) %>%
      dplyr::select(
        group,
        subgroup1,
        subgroup2,
        prop_diff,
        z_score,
        p_value,
        ci_lower,
        ci_upper,
        adj_p_value
      )
  } else {
    results <- results %>%
      mutate(adj_p_value = NA) %>%
      dplyr::select(
        group,
        subgroup1,
        subgroup2,
        prop_diff,
        z_score,
        p_value,
        ci_lower,
        ci_upper,
        adj_p_value
      )
  }
  
  return(results)
}





######---Define theme---######



theme_nice <- ggthemes::theme_tufte() +
  theme(
    axis.ticks = element_line(linewidth = 0.5, color = "black"),
    axis.ticks.length = unit(4, "mm"),
    plot.title = element_text(
      family = "Sofia Sans Condensed",
      size = 20,
      hjust = 0,
      vjust = 2
    ),
    plot.subtitle = element_text(
      family = "Sofia Sans Condensed", 
      size = 18),
    plot.caption = element_text(
      family = "Sofia Sans Condensed",
      size = 16,
      hjust = 1
    ),
    axis.title = element_text(
      family = "Sofia Sans Condensed", 
      size = 18),
    axis.text = element_text(
      family = "Sofia Sans Condensed", 
      size = 18),
    axis.text.x = element_text(margin = margin(5, b = 10)),
    strip.text = element_text(
      family = "Sofia Sans Condensed", 
      size = 18)
  )

# Set the defined theme as the default theme
theme_set(theme_nice)


######---Load data---######

eu <- read_excel("eu-data.xlsx") |>
  janitor::clean_names() |>
  filter(ic == "Yes" &
           diagnosis_prevention_research_or_clinical_management == "1")

eu

###---Load map data---###


europe <- c(
  "Albania",
  "Austria",
  "Belgium",
  "Bulgaria",
  "Bosnia and Herzegovina",
  "Belarus",
  "Switzerland",
  "Czech Republic",
  "Germany",
  "Denmark",
  "Spain",
  "Estonia",
  "Finland",
  "France",
  "UK",
  "Greece",
  "Croatia",
  "Hungary",
  "Ireland",
  "Italy",
  "Kosovo",
  "Lithuania",
  "Luxembourg",
  "Latvia",
  "Moldova",
  "Malta",
  "North Macedonia",
  "Montenegro",
  "Netherlands",
  "Norway",
  "Poland",
  "Portugal",
  "Romania",
  "Serbia",
  "Slovakia",
  "Slovenia",
  "Sweden",
  "Ukraine",
  "Cyprus"
)

hce <- read_csv("hcep.csv") |>
  janitor::clean_names() |>
  filter(period == "2021" & parent_location == "Europe") |>
  dplyr::select(country = location, hcepc = fact_value_numeric) |>
  mutate(
    country = case_when(
      country == "United Kingdom of Great Britain and Northern Ireland" ~ "UK",
      country == "Czechia" ~ "Czech Republic",
      country == "Netherlands (Kingdom of the)" ~ "Netherlands",
      TRUE ~ country
    )
  ) |>
  filter(country %in% europe)

eu <- eu |>
  left_join(hce, by = "country") |>
  mutate(hcepc_hight = ifelse(hcepc > mean(hcepc, na.rm = TRUE), "1", "0"))



####---Plot---####

map_data("world", region = europe) |>
  tibble() |>
  filter(lat < 72) |>
  filter(!subregion %in% c("Jan Mayen", "Mageroya", "Soroya")) |>
  left_join(eu |>
              count(region = country)) |>
  mutate(included = ifelse(is.na(n), "NO", "YES")) |>
  ggplot(aes(x = long, y = lat, group = group)) +
  geom_polygon(
    aes(fill = n),
    alpha = 0.7,
    color = "black",
    lty = 1,
    linewidth = 0.2
  ) +
  theme_void() +
  theme(legend.position = "none") +
  scale_fill_gradient2(
    midpoint = 4,
    low = "#FFC96F",
    mid = "#68D2E8",
    high = "#003285"
  )


# ggsave(
#   "eu-response.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 11,
#   height = 11
# )

### Univariate analysis of demographic variables ###

eu |> dplyr::select(hcepc_hight) |> table() |> rstatix::chisq_test()

eu |> count(country, sort = T)

# eu |> dplyr::select(5, 7:41) |>
#   gtsummary::tbl_summary() |>
#   as_flex_table()

eu |>
  dplyr::select(starts_with("workplace_")) |>
  dplyr::select(-5) |>
  pivot_longer(cols = everything(),
               names_to = "workplace",
               values_to = "value") |>  table() |>
  effectsize::cramers_v()


eu |>
  dplyr::select(starts_with("specialty_")) |>
  dplyr::select(-8) |>
  pivot_longer(cols = everything(),
               names_to = "specialty",
               values_to = "value") |>  table() |>
  #rstatix::chisq_test() |>
  effectsize::cramers_v()

eu |>
  count(age_group_of_patients) |>
  mutate(sum = sum(n)) |>
  pcit() |>
  compare_proportions()

eu |>
  dplyr::select(age_group_of_patients) |>
  table() |>
  rstatix::chisq_test()


eu |>
  dplyr::select(starts_with("area_of_rare_cancers_")) |>
  pivot_longer(cols = 1:12,
               names_to = "area",
               values_to = "value") |>
  table() |>
  pairwise_prop_test()

eu |>
  dplyr::select(starts_with("area_of_rare_cancers_")) |>
  pivot_longer(cols = 1:12,
               names_to = "area",
               values_to = "value") |>
  group_by(value) |>
  count(area) |>
  ungroup() |>
  filter(value == 1) |>
  dplyr::select(-value) |>
  mutate(sum = sum(n)) |>
  pcit() |>
  compare_proportions(method = "hommel")

eu |>
  dplyr::select(starts_with("area_of_rare_cancers_")) |>
  pivot_longer(cols = 1:12,
               names_to = "area",
               values_to = "value") |>
  mutate(value = as_factor(value)) |>
  prop_test(value ~ area)

eu |>
  dplyr::select(starts_with("area_of_rare_cancers_")) |>
  pivot_longer(cols = 1:12,
               names_to = "area",
               values_to = "value") |>
  table() |>
  pairwise.prop.test() |>
  model_parameters() |>
  tibble()

## Demographic variables by strata ##

# eu |>
#   dplyr::select(5, 7:41, 174) |>
#   dplyr::select(-c(9, 17)) |>
#   gtsummary::tbl_summary(by = hcepc_hight) |>
#   add_difference() |>
#   as_flex_table()

eu |>
  count(hcepc_hight, age_group_of_patients) |>
  group_by(hcepc_hight) |>
  mutate(sum = sum(n),
         group = paste(hcepc_hight, age_group_of_patients)) |>
  ungroup() |>
  dplyr::select(5, 3, 4) |>
  pcit() |>
  compare_proportions(method = "bonferroni")


### Multivariate analysis of demographic variables ###

eu |>
  count(hcepc_hight, age_group_of_patients) |>
  group_by(hcepc_hight) |>
  mutate(sum = sum(n)) |>
  pcit() |>
  compare_proportions_by()


eu |>
  count(hcepc_hight, main_focus_of_your_professional_activities) |>
  group_by(hcepc_hight) |>
  mutate(sum = sum(n)) |>
  pcit() |>
  compare_proportions_by()


# eu |>
#   dplyr::select(5, 7:41, 174) |>
#   dplyr::select(-c(9, 17)) |>
#   gtsummary::tbl_summary(by = male) |>
#   add_difference() |>
#   as_flex_table()

eu |>
  count(male, main_focus_of_your_professional_activities) |>
  group_by(male) |>
  mutate(sum = sum(n), male = as_factor(male)) |>
  pcit() |>
  compare_proportions_by() |>
  mutate_if(is.numeric, round, 3) |>
  flextable::flextable()


# eu |>
#   dplyr::select(5, 7:41, 174) |>
#   dplyr::select(-c(9, 17)) |>
#   gtsummary::tbl_summary(by = age_group_of_patients) |>
#   add_p() |>
#   as_flex_table()

# eu |>
#   dplyr::select(5, 7:41, 174) |>
#   dplyr::select(-c(9, 17)) |>
#   mutate(expertise = ifelse(cancer_exp_years > 17.5, 1, 0)) |>
#   gtsummary::tbl_summary(by = expertise) |>
#   add_p() |>
#   as_flex_table()


# eu |>
#   dplyr::select(5, 7:41, 174) |>
#   dplyr::select(-c(9, 17)) |>
#   gtsummary::tbl_summary(by = specialty_oncology) |>
#   add_p() |>
#   as_flex_table()

# eu |>
#   dplyr::select(5, 7:41, 174) |>
#   dplyr::select(-c(9, 17)) |>
#   mutate(
#     clinical = ifelse(
#       main_focus_of_your_professional_activities == "Clinical diagnosis and # management",
#       1,
#       0
#     )
#   ) |>
#   gtsummary::tbl_summary(by = clinical) |>
#   add_p() |>
#   as_flex_table()


### General policies ###

gp <-
  eu |>
  dplyr::select(5:41, 42:59, 174)

gp |>
  count(legal_definition_of_rare_cancers) |>
  mutate(sum = sum(n)) |>
  pcit() |>
  compare_proportions() |>
  mutate_if(is.numeric, round, 3)

gp |>
  dplyr::select(legal_definition_of_rare_cancers) |>
  table() |>
  rstatix::chisq_test()

# gp |>
#   dplyr::select(1:38) |>
#   dplyr::select(-c("country",10, 18)) |>
#   tbl_summary(by = legal_definition_of_rare_cancers) |>
#   add_p() |>
#   as_flex_table()


# gp |>
#   dplyr::select(1:37,39) |>
#   dplyr::select(-c("country",10, 18)) |>
#   tbl_summary(by = rare_cancers_defined_as_a_priority_group) |>
#   add_p() |>
#   as_flex_table()

gp |>
  count(hcepc_hight, legal_definition_of_rare_cancers) |>
  group_by(hcepc_hight) |>
  mutate(sum = sum(n), hcepc_hight = as_factor(hcepc_hight)) |>
  pcit() |>
  compare_proportions_by()


gp |>
  dplyr::select(hcepc_hight, legal_definition_of_rare_cancers) |>
  table() |>
  rstatix::chisq_test()




gp |>
  count(legal_definition_of_rare_cancers) |>
  mutate(sum = sum(n)) |>
  pcit() |>
  mutate(
    legal_definition_of_rare_cancers =
      case_when(
        legal_definition_of_rare_cancers == "No, but the general definition for rare diseases is applied." ~ "Използва се дефиницията за редки болести",
        legal_definition_of_rare_cancers == "No" ~ "Без нормативна дефиниция",
        legal_definition_of_rare_cancers == "Yes" ~ "С нормативна дефиниция",
        TRUE ~ legal_definition_of_rare_cancers
      )
  ) |>
  ggplot(aes(
    x = proportion,
    y = fct_reorder(legal_definition_of_rare_cancers, proportion),
    fill = legal_definition_of_rare_cancers
  )) +
  geom_col(width = .5, color = "gray10") +
  geom_rangeframe(
    data = tibble(
      legal_definition_of_rare_cancers =
        c(
          "Използва се дефиницията за редки болести",
          "Без нормативна дефиниция",
          "С нормативна дефиниция"
        ),
      proportion =
        c(0, 0 / 5, 0.6)
    ),
    sides = "b"
  ) +
  geom_text(
    aes(label = legal_definition_of_rare_cancers, x = 0),
    family = "Sofia Sans Condensed",
    #fontface = "bold",
    hjust = 0,
    vjust = -2.8,
    size = 7
  ) +
  geom_errorbarh(
    aes(xmin = lower, xmax = upper),
    height = 0.2,
    size = 0.3,
    color = "gray10",
    lty = 1,
    alpha = 0.7
  ) +
  geom_label(
    aes(label = paste0("  ", sprintf(
      "%2.1f", proportion * 100
    ), "%  ")),
    #color = proportion > .05
    #hjust = proportion > .05),
    fill = "white",
    size = 5,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  scale_color_manual(values = c("black", "white"), guide = "none") +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(-0.1, 0.7),
    breaks = c(seq(0, 0.6, 0.2)),
    labels = scales::label_percent()
  ) +
  scale_y_discrete(guide = "none") +
  scale_fill_manual(values = c("gray80", "#37B7C3", "gray80")) +
  theme(
    legend.position = "none",
    axis.title.y = element_blank(),
    axis.text.y = element_blank(),
    axis.ticks.y = element_blank(),
    axis.line.y = element_blank()
  ) +
  labs(y = "", x = "")

# ggsave(
#   "legal-definition-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 20,
#   height = 15
# )



gp |>
  count(hcepc_hight, rare_cancers_defined_as_a_priority_group) |>
  group_by(hcepc_hight) |>
  mutate(
    sum = sum(n),
    rare_cancers_defined_as_a_priority_group = as_factor(rare_cancers_defined_as_a_priority_group),
    hcepc_hight = as_factor(hcepc_hight)
  ) |>
  mutate(
    hcepc_hight = case_when(
      hcepc_hight == "1" ~ "hcepc_hight",
      hcepc_hight == "0" ~ "hcepc_low"
    ),
    rare_cancers_defined_as_a_priority_group = case_when(
      rare_cancers_defined_as_a_priority_group == "1" ~ "Priority",
      rare_cancers_defined_as_a_priority_group == "0" ~ "Not priority"
    )
  ) |>
  ungroup() |>
  pcit() |>
  compare_proportions_by()


gp |>
  count(hcepc_hight, rare_cancers_defined_as_a_priority_group) |>
  group_by(hcepc_hight) |>
  mutate(
    sum = sum(n),
    rare_cancers_defined_as_a_priority_group = as_factor(rare_cancers_defined_as_a_priority_group),
    hcepc_hight = as_factor(hcepc_hight)
  ) |>
  mutate(
    hcepc_hight = case_when(
      hcepc_hight == "1" ~ "hcepc_hight",
      hcepc_hight == "0" ~ "hcepc_low"
    ),
    rare_cancers_defined_as_a_priority_group = case_when(
      rare_cancers_defined_as_a_priority_group == "1" ~ "Priority",
      rare_cancers_defined_as_a_priority_group == "0" ~ "Not priority"
    )
  ) |>
  ungroup() |>
  filter(rare_cancers_defined_as_a_priority_group == "Priority") |>
  dplyr::select(-rare_cancers_defined_as_a_priority_group) |>
  mutate(prop = n / sum, pdiff_hight_low = prop - lag(prop)) |>
  dplyr::select(pdiff_hight_low) |>
  filter(!is.na(pdiff_hight_low))




set.seed(123)
bstpriority <-
  gp  |>
  rsample::bootstraps(1000) |>
  mutate(
    pdiff_hight_low = map(
      splits,
      ~ analysis(.x) |>
        count(hcepc_hight, rare_cancers_defined_as_a_priority_group) |>
        group_by(hcepc_hight) |>
        mutate(
          sum = sum(n),
          rare_cancers_defined_as_a_priority_group = as_factor(rare_cancers_defined_as_a_priority_group),
          hcepc_hight = as_factor(hcepc_hight)
        ) |>
        mutate(
          hcepc_hight = case_when(
            hcepc_hight == "1" ~ "hcepc_hight",
            hcepc_hight == "0" ~ "hcepc_low"
          ),
          rare_cancers_defined_as_a_priority_group = case_when(
            rare_cancers_defined_as_a_priority_group == "1" ~ "Priority",
            rare_cancers_defined_as_a_priority_group == "0" ~ "Not priority"
          )
        ) |>
        ungroup() |>
        filter(rare_cancers_defined_as_a_priority_group == "Priority") |>
        dplyr::select(-rare_cancers_defined_as_a_priority_group) |>
        mutate(prop = n / sum, pdiff_hight_low = prop - lag(prop)) |>
        dplyr::select(pdiff_hight_low) |>
        filter(!is.na(pdiff_hight_low))
    )
  ) |>
  unnest(pdiff_hight_low)



bstpriority |>
  ggplot(aes(x = pdiff_hight_low)) +
  stat_slab(aes(fill_ramp = after_stat(cut_cdf_qi(
    cdf, .width = c(0.02, 0.8, 0.95, 1)
  ))), fill = "#37B7C3") +
  scale_fill_ramp_discrete(range = c(1, 0.2), guide = "none") +
  geom_vline(xintercept = 0,
             lty = 2,
             color = "gray80") +
  ggthemes::geom_rangeframe(data = tibble(pdiff_hight_low = c(0, 0.8)), sides = "b") +
  scale_x_continuous(labels = scales::label_percent(),
                     breaks = seq(0, 0.8, 0.2)) +
  labs(x = "% разлика в приоритизирането на редките тумори в страни с високи ПРЗГН") +
  theme(
    legend.position = "none",
    axis.title.y = element_blank(),
    axis.text.y = element_blank(),
    axis.ticks.y = element_blank(),
    axis.line.y = element_blank()
  )

# ggsave(
#   "priority-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 20,
#   height = 10
# )

# gp |>
#   dplyr::select(40:47) |>
#   get_summary_stats() |>
#   mutate_if(is.numeric, round, 3) |>
#   dplyr::select(variable, mean, sd) |>
#   knitr::kable()


gp |>
  dplyr::select(40:47) |>
  get_summary_stats() |>
  ggplot(aes(x = mean, y = fct_reorder(variable, mean))) +
  geom_point(size = 3) +
  geom_rangeframe(data = tibble(
    variable = c(
      "ncp_efficiency",
      "ncp_equity",
      "ncp_evidence_based_interventions",
      "ncp_funding",
      "ncp_goals_and_objectives",
      "ncp_implementation_strategy",
      "ncp_monitoring_and_evaluation",
      "ncp_stakeholder_engagemnt"
    ),
    mean = c(1, 5, 1, 1, 1, 1, 1, 1)
  )) +
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.2f", mean
    ))),
    hjust = +0.5,
    vjust = -0.5,
    size = 5,
    family = "Sofia Sans Condensed"
  ) +
  geom_errorbar(
    aes(xmin = mean - 1.96 * se, xmax = mean + 1.96 * se),
    width = 0.2,
    size = 0.5,
    color = "gray10"
  ) +
  geom_vline(
    xintercept = 3.26,
    lty = 2,
    size = 0.5,
    color = "gray10"
  ) +
  scale_y_discrete(
    labels = c(
      "ncp_efficiency" = "Ефективност",
      "ncp_equity" = "Равенство",
      "ncp_evidence_based_interventions" = "Основани на доказателства \nинтервенции",
      "ncp_funding" = "Финансиране",
      "ncp_goals_and_objectives" = "Ясни цели и задачи",
      "ncp_implementation_strategy" = "Стратегия за прилагане",
      "ncp_monitoring_and_evaluation" = "Мониторинг и оценка",
      "ncp_stakeholder_engagemnt" = "Ангажираност на \nзаинтересованите страни"
    )
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(1, 5.5),
    breaks = c(seq(1, 5, 1))
  ) +
  labs(x = "", y = "", subtitle = "")

#  ggsave("ncp-mean-bg.png",
#         device = "png",
#         bg = "white",
#         units = "mm",
#         width = 200,
#         height = 130,
#         dpi = 1000)

gp |>
  dplyr::select(40:47) |>
  pivot_longer(cols = 1:8,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    fct_var = case_when(
      value == 1 ~ "no",
      value == 2 ~ "no",
      value == 3 ~ "both",
      value == 4 ~ "yes",
      value == 5 ~ "yes"
    )
  ) |>
  count(variable, fct_var) |>
  group_by(variable) |>
  pivot_wider(names_from = fct_var, values_from = n) |>
  mutate(
    agreement = (yes + 0.5 * both) / 92,
    disagreement = (no + 0.5 * both) / 92,
    adr = agreement / disagreement,
    adr1 = ifelse(adr > 1, TRUE, FALSE)
  ) |>
  dplyr::select(variable, agreement, disagreement, adr, adr1) |>
  ggplot(aes(
    x = agreement,
    y = fct_reorder(variable, agreement),
    fill = adr1
  )) +
  geom_col(color = "gray10", alpha = 0.7) +
  geom_vline(
    xintercept = 0.5,
    lty = 2,
    size = 0.5,
    color = "#013440"
  ) +
  geom_rangeframe(data = tibble(
    variable = c(
      "ncp_efficiency",
      "ncp_equity",
      "ncp_evidence_based_interventions",
      "ncp_funding",
      "ncp_goals_and_objectives",
      "ncp_implementation_strategy",
      "ncp_monitoring_and_evaluation",
      "ncp_stakeholder_engagemnt"
    ),
    agreement = c(0, 1, 0, 0, 0, 0, 0, 0),
    adr1 = c(FALSE, FALSE, FALSE, TRUE, FALSE, FALSE, FALSE, FALSE)
  )) +
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.1f", agreement * 100
    ), "%  ")),
    #color = agreement > .05
    #hjust = agreement > .05),
    hjust = "right",
    size = 5,
    family = "Roboto Condensed",
  ) +
  scale_fill_manual(values = generate_palette("#37B7C3", 
                                                modification = "go_both_ways", 
                                                n_colours = 2))+
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(-0.05, 1.1),
    breaks = c(seq(0, 1, 0.2)),
    labels = scales::label_percent()
  ) +
  scale_y_discrete(
    labels = c(
      "ncp_efficiency" = "Ефективност",
      "ncp_equity" = "Равенство",
      "ncp_evidence_based_interventions" = "Основани на доказателства \nинтервенции",
      "ncp_funding" = "Финансиране",
      "ncp_goals_and_objectives" = "Ясни цели и задачи",
      "ncp_implementation_strategy" = "Стратегия за прилагане",
      "ncp_monitoring_and_evaluation" = "Мониторинг и оценка",
      "ncp_stakeholder_engagemnt" = "Ангажираност на \nзаинтересованите страни"
    )
  ) +
  theme(legend.position = "none") +
  labs(y = "", x = "%Одобрение")

# ggsave(
#   "ncp-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 24,
#   height = 12
# )


gp |>
  dplyr::select(40:47) |>
  pivot_longer(cols = 1:8,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    variable = case_when(
      variable == "ncp_efficiency" ~ "Ефективност",
      variable == "ncp_equity" ~ "Равенство",
      variable == "ncp_evidence_based_interventions" ~ "Основани на доказателства интервенции",
      variable == "ncp_funding" ~ "Финансиране",
      variable == "ncp_goals_and_objectives" ~ "Ясни цели и задачи",
      variable == "ncp_implementation_strategy" ~ "Стратегия за прилагане",
      variable == "ncp_monitoring_and_evaluation" ~ "Мониторинг и оценка",
      variable == "ncp_stakeholder_engagemnt" ~ "Ангажираност на заинтересованите страни"
    )
  ) |>
  aov(value ~ variable, data = _) |>
  model_parameters()

gp |>
  dplyr::select(40:47) |>
  pivot_longer(cols = 1:8,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    variable = case_when(
      variable == "ncp_efficiency" ~ "Ефективност",
      variable == "ncp_equity" ~ "Равенство",
      variable == "ncp_evidence_based_interventions" ~ "Основани на доказателства интервенции",
      variable == "ncp_funding" ~ "Финансиране",
      variable == "ncp_goals_and_objectives" ~ "Ясни цели и задачи",
      variable == "ncp_implementation_strategy" ~ "Стратегия за прилагане",
      variable == "ncp_monitoring_and_evaluation" ~ "Мониторинг и оценка",
      variable == "ncp_stakeholder_engagemnt" ~ "Ангажираност на заинтересованите страни"
    )
  ) |>
  aov(value ~ variable, data = _) |>
  effectsize::eta_squared()




gp |>
  dplyr::select(40:47) |>
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
    Parameter1 = case_when(
      Parameter1 == "ncp_efficiency" ~ "Ефективност",
      Parameter1 == "ncp_equity" ~ "Равенство",
      Parameter1 == "ncp_evidence_based_interventions" ~ "Основани на доказателства интервенции",
      Parameter1 == "ncp_funding" ~ "Финансиране",
      Parameter1 == "ncp_goals_and_objectives" ~ "Ясни цели и задачи",
      Parameter1 == "ncp_implementation_strategy" ~ "Стратегия за прилагане",
      Parameter1 == "ncp_monitoring_and_evaluation" ~ "Мониторинг и оценка",
      Parameter1 == "ncp_stakeholder_engagemnt" ~ "Ангажираност на заинтересованите страни"
      ),
    Parameter2 = case_when(
        Parameter2 == "ncp_efficiency" ~ "Ефективност",
        Parameter2 == "ncp_equity" ~ "Равенство",
        Parameter2 == "ncp_evidence_based_interventions" ~ "Основани на доказателства интервенции",
        Parameter2 == "ncp_funding" ~ "Финансиране",
        Parameter2 == "ncp_goals_and_objectives" ~ "Ясни цели и задачи",
        Parameter2 == "ncp_implementation_strategy" ~ "Стратегия за прилагане",
        Parameter2 == "ncp_monitoring_and_evaluation" ~ "Мониторинг и оценка",
        Parameter2 == "ncp_stakeholder_engagemnt" ~ "Ангажираност на заинтересованите страни"),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 45, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))


# ggsave(
#   "ncp-full-cor-criteria-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 26,
#   height = 16
# 
# )

gp |>
  dplyr::select(40:47) |>
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
    Parameter1 = case_when(
      Parameter1 == "ncp_efficiency" ~ "Efficiency",
      Parameter1 == "ncp_equity" ~ "Equity",
      Parameter1 == "ncp_evidence_based_interventions" ~ "EVidence based interventions",
      Parameter1 == "ncp_funding" ~ "Funding",
      Parameter1 == "ncp_goals_and_objectives" ~ "Goals and objectives",
      Parameter1 == "ncp_implementation_strategy" ~ "Implementation strategy",
      Parameter1 == "ncp_monitoring_and_evaluation" ~ "Monitoring and evaluation",
      Parameter1 == "ncp_stakeholder_engagemnt" ~ "Stakeholder engagement"
    ),
    Parameter2 = case_when(
      Parameter2 == "ncp_efficiency" ~ "Efficiency",
      Parameter2 == "ncp_equity" ~ "Equity",
      Parameter2 == "ncp_evidence_based_interventions" ~ "EVidence based interventions",
      Parameter2 == "ncp_funding" ~ "Funding",
      Parameter2 == "ncp_goals_and_objectives" ~ "Goals and objectives",
      Parameter2 == "ncp_implementation_strategy" ~ "Implementation strategy",
      Parameter2 == "ncp_monitoring_and_evaluation" ~ "Monitoring and evaluation",
      Parameter2 == "ncp_stakeholder_engagemnt" ~ "Stakeholder engagement"
    ),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 45, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))

# ggsave(
#   "ncp-full-cor-criteria-en.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 26,
#   height = 16
# 
# )
 
gp |>
  dplyr::select(40:47) |>
  pivot_longer(cols = 1:8,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    variable = case_when(
      variable == "ncp_efficiency" ~ "Ефективност",
      variable == "ncp_equity" ~ "Равенство",
      variable == "ncp_evidence_based_interventions" ~ "Основани на доказателства интервенции",
      variable == "ncp_funding" ~ "Финансиране",
      variable == "ncp_goals_and_objectives" ~ "Ясни цели и задачи",
      variable == "ncp_implementation_strategy" ~ "Стратегия за прилагане",
      variable == "ncp_monitoring_and_evaluation" ~ "Мониторинг и оценка",
      variable == "ncp_stakeholder_engagemnt" ~ "Ангажираност на заинтересованите страни"
    )
  ) |>
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(specs = "variable") |>
  broom::tidy() |>
  arrange(estimate) |>
  dplyr::select(1:3) |>
  mutate(lower = estimate - 1.96 * std.error,
         upper = estimate + 1.96 * std.error)

gp |>
  dplyr::select(40:47) |>
  psych::KMO()

gp |>
  dplyr::select(40:47) |>
  psych::cortest.bartlett()

gp |>
  dplyr::select(40:47) |>
  correlation() |>
  tibble() |>
  mutate(
    Parameter1   = case_when(
      Parameter1   == "ncp_efficiency" ~ "Ефективност",
      Parameter1   == "ncp_equity" ~ "Равенство",
      Parameter1   == "ncp_evidence_based_interventions" ~ "Основани на доказателства интервенции",
      Parameter1   == "ncp_funding" ~ "Финансиране",
      Parameter1   == "ncp_goals_and_objectives" ~ "Ясни цели и задачи",
      Parameter1 == "ncp_implementation_strategy" ~ "Стратегия за прилагане",
      Parameter1 == "ncp_monitoring_and_evaluation" ~ "Мониторинг и оценка",
      Parameter1 == "ncp_stakeholder_engagemnt" ~ "Ангажираност на заинтересованите страни"
    ),
    Parameter2   = case_when(
      Parameter2   == "ncp_efficiency" ~ "Ефективност",
      Parameter2   == "ncp_equity" ~ "Равенство",
      Parameter2   == "ncp_evidence_based_interventions" ~ "Основани на доказателства интервенции",
      Parameter2   == "ncp_funding" ~ "Финансиране",
      Parameter2   == "ncp_goals_and_objectives" ~ "Ясни цели и задачи",
      Parameter2 == "ncp_implementation_strategy" ~ "Стратегия за прилагане",
      Parameter2 == "ncp_monitoring_and_evaluation" ~ "Мониторинг и оценка",
      Parameter2 == "ncp_stakeholder_engagemnt" ~ "Ангажираност на заинтересованите страни"
    )
  ) |>
  mutate_if(is.numeric, round, 2) |>
  mutate(CI = paste0("[", CI_low, ", ", CI_high, "]")) |>
  dplyr::select(Parameter1, Parameter2, r, CI, p) |>
  knitr::kable()


gp |>
  dplyr::select(40:47) |>
  pivot_longer(cols = 1:8,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    variable = case_when(
      variable == "ncp_efficiency" ~ "Ефективност",
      variable == "ncp_equity" ~ "Равенство",
      variable == "ncp_evidence_based_interventions" ~ "Основани на доказателства интервенции",
      variable == "ncp_funding" ~ "Финансиране",
      variable == "ncp_goals_and_objectives" ~ "Ясни цели и задачи",
      variable == "ncp_implementation_strategy" ~ "Стратегия за прилагане",
      variable == "ncp_monitoring_and_evaluation" ~ "Мониторинг и оценка",
      variable == "ncp_stakeholder_engagemnt" ~ "Ангажираност на заинтересованите страни"
    )
  ) |>
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(specs = "variable") |>
  pairs(adjust = "Bonferroni") |>
  tidy() |>
  dplyr::select(2, 4, 5, 7, 8) |>
  mutate_if(is.numeric, round, 2) |>
  knitr::kable()


gp |>
  dplyr::select(2, 40:47) |>
  pivot_longer(cols = 2:9,
               names_to = "variable",
               values_to = "value") |>
  aov(value ~ variable + country  , data = _) |>
  model_parameters()

map_ncp <-
  gp |>
  dplyr::select(2, 40:47) |>
  mutate(ncpsum = rowSums(across(where(is.numeric)))) |>
  dplyr::select(1, 10) |>
  group_by(country) |>
  get_summary_stats() |>
  dplyr::select(country, mean)



gp |>
  dplyr::select(2, 40:47) |>
  mutate(ncpsum = rowSums(across(where(is.numeric)))) |>
  dplyr::select(1, 10) |>
  aov(ncpsum ~ country, data = _) |>
  model_parameters()

gp |>
  dplyr::select(2, 40:47) |>
  mutate(ncpsum = rowSums(across(where(is.numeric)))) |>
  dplyr::select(1, 10) |>
  aov(ncpsum ~ country, data = _) |>
  emmeans::emmeans(specs = "country", adjust = "sidak") |>
  tidy() |>
  arrange(-estimate) |>
  mutate(
    lower = estimate - 1.96 * std.error,
    upper = estimate + 1.96 * std.error,
    "95%CI" = paste0("[", round(lower, 2), ", ", round(upper, 2), "]")
  ) |>
  mutate_if(is.numeric, round, 2) |>
  dplyr::select(1, 2, 5, 9) |>
  knitr::kable()


eu_countries <-
  map_data("world", region = europe) |>
  tibble() |>
  rename(country = region) |>
  filter(lat < 72) |>
  filter(!subregion %in% c("Jan Mayen", "Mageroya", "Soroya"))

eu_countries |>
  left_join(map_ncp) |>
  ggplot(aes(x = long, y = lat, group = group)) +
  geom_polygon(
    aes(fill = mean),
    alpha = 1.4,
    color = "black",
    lty = 1,
    linewidth = 0.2
  ) +
  theme_void() +
  theme(legend.position = "none") +
  scale_fill_gradient2(
    midpoint = 26.4,
    low = "#FFC96F",
    mid = "#68D2E8",
    high = "#003285"
  )


#  ggsave(
#    "eu-ncp-map.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 11,
#    height = 11
#  )

gp |>
  dplyr::select(40:47) |>
  pivot_longer(cols = 1:8,
               names_to = "variable",
               values_to = "value") |>
  aov(value ~ variable, data = _) |>
  avg_comparisons(by = "variable") |>
  tibble()



gp |>
  dplyr::select(48:54) |>
  get_summary_stats() |>
  mutate_if(is.numeric, round, 3) |>
  dplyr::select(variable, mean, sd) |>
  knitr::kable()


gp |>
  dplyr::select(48:54) |>
  pivot_longer(cols = 1:7,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    fct_var = case_when(
      value == 1 ~ "no",
      value == 2 ~ "no",
      value == 3 ~ "both",
      value == 4 ~ "yes",
      value == 5 ~ "yes"
    )
  ) |>
  count(variable, fct_var) |>
  group_by(variable) |>
  pivot_wider(names_from = fct_var, values_from = n) |>
  mutate(
    agreement = (yes + 0.5 * both) / 92,
    disagreement = (no + 0.5 * both) / 92,
    adr = agreement / disagreement,
    adr1 = ifelse(adr > 1, TRUE, FALSE)
  ) |>
  dplyr::select(variable, agreement, disagreement, adr, adr1) |>
  ggplot(aes(
    x = agreement,
    y = fct_reorder(variable, agreement),
    fill = adr1
  )) +
  geom_col(color = "gray10", alpha = 0.7) +
  geom_vline(
    xintercept = 0.5,
    lty = 2,
    size = 0.5,
    color = "#013440"
  ) +
  geom_rangeframe(data = tibble(
    variable = c(
      "ncp_funding_other_eu_financing_project_lines",
      "ncp_funding_other_industry",
      "ncp_funding_other_non_profit_institutions_serving_households",
      "ncp_funding_private_household_out_of_pocket_expenditure",
      "ncp_funding_private_voluntary_health_insurance_funding",
      "ncp_funding_public_goverment_funding",
      "ncp_funding_public_health_insurance_funding"
    ),
    agreement = c(0, 1, 0, 0, 0, 0, 0),
    adr1 = c(FALSE, FALSE, TRUE, FALSE, FALSE, FALSE, FALSE)
  )) +
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.1f", agreement * 100
    ), "%  ")),
    #color = agreement > .05
    #hjust = agreement > .05),
    hjust = "right",
    size = 5,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  scale_fill_manual(values = c("gray85", "#37B7C3")) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(-0.05, 1.1),
    breaks = c(seq(0, 1, 0.2)),
    labels = scales::label_percent()
  ) +
  scale_y_discrete(
    labels = c(
      "ncp_funding_other_eu_financing_project_lines" = "Програми и фондове на ЕС",
      "ncp_funding_other_industry" = "Индустрия",
      "ncp_funding_other_non_profit_institutions_serving_households" = "Финансиране от НПО",
      "ncp_funding_private_household_out_of_pocket_expenditure" = "Лични разходи на домакинствата",
      "ncp_funding_private_voluntary_health_insurance_funding" = "ДОФ",
      "ncp_funding_public_goverment_funding" = "Държавно финансиране",
      "ncp_funding_public_health_insurance_funding" = "ЗОФ"
    )
  ) +
  theme(legend.position = "none") +
  labs(y = "", x = "%Одобрение")

# ggsave(
#   "ncp-finance-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 24,
#   height = 12
# )



gp |>
  count(approaches_for_rare_cancer_policies) |>
  mutate(sum = sum(n)) |>
  pcit() |>
  mutate(
    approaches_for_rare_cancer_policies =
      case_when(
        approaches_for_rare_cancer_policies == "Aligning rare cancer policies with all other cancer-related policies" ~ "Съгласуване с онкологичните политики",
        approaches_for_rare_cancer_policies == "Aligning rare cancer policies with other policies related to rare diseases" ~ "Съгласуване с политиките за редки болести",
        approaches_for_rare_cancer_policies == "Establishing rare cancer policies as a distinct area of policies" ~ "Изграждане на самостоятелни политики",
        TRUE ~ approaches_for_rare_cancer_policies
      )
  ) |>
  ggplot(aes(
    x = proportion,
    y = fct_reorder(approaches_for_rare_cancer_policies, proportion),
    fill = approaches_for_rare_cancer_policies
  )) +
  geom_col(width = .5, color = "gray10") +
  geom_rangeframe(
    data = tibble(
      approaches_for_rare_cancer_policies =
        c(
          "Съгласуване с онкологичните политики",
          "Съгласуване с политиките за редки болести",
          "Изграждане на самостоятелни политики"
        ),
      proportion =
        c(0, 0.5, 0.6)
    ),
    sides = "b"
  ) +
  geom_text(
    aes(label = approaches_for_rare_cancer_policies, x = 0),
    family = "Sofia Sans Condensed",
    #fontface = "bold",
    hjust = 0,
    vjust = -2.8,
    size = 7
  ) +
  geom_errorbarh(
    aes(xmin = lower, xmax = upper),
    height = 0.2,
    size = 0.3,
    color = "gray10",
    lty = 1,
    alpha = 0.7
  ) +
  geom_label(
    aes(label = paste0("  ", sprintf(
      "%2.1f", proportion * 100
    ), "%  ")),
    #color = proportion > .05
    #hjust = proportion > .05),
    fill = "white",
    size = 5,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  scale_color_manual(values = c("black", "white"), guide = "none") +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(-0.1, 0.7),
    breaks = c(seq(0, 0.6, 0.2)),
    labels = scales::label_percent()
  ) +
  scale_y_discrete(guide = "none") +
  scale_fill_manual(values = c("gray80", "#37B7C3", "gray80")) +
  theme(
    legend.position = "none",
    axis.title.y = element_blank(),
    axis.text.y = element_blank(),
    axis.ticks.y = element_blank(),
    axis.line.y = element_blank()
  ) +
  labs(y = "", x = "")


# ggsave(
#   "approaches-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 20,
#   height = 15
# )



gp |>
  count(ncp_stakeholder_engagemnt, ncp_equity) |>
  full_join(expand.grid(
    ncp_stakeholder_engagemnt = 1:5,
    ncp_equity = 1:5
  )) |>
  mutate(n = ifelse(is.na(n), 0, n),
         sum = sum(n),
         prop = n / sum) |>
  ggplot(aes(x = ncp_equity, y = ncp_stakeholder_engagemnt)) +
  geom_tile(
    aes(fill = prop),
    color = "white",
    alpha = 0.9,
    linewidth = 1
  ) +
  geom_text(
    aes(label = ifelse(prop > 0,
          paste0("  ", sprintf(
      "%2.1f", prop * 100
    ), "%  "),
          ""
    )),
    vjust = 0.5,
    hjust = 0.5,
    size = 5,
    family = "Roboto Condensed",
  ) +
  geom_rangeframe(data = tibble(
    ncp_stakeholder_engagemnt = c(1, 2, 3, 4, 5),
    ncp_equity = c(1, 2, 3, 4, 5)
  )) +
  scale_fill_gradient2(
    midpoint = 0.09,
    low = "white",
    mid = "#31B1C2",
    high = "#021526"
  ) +
  theme(legend.position = "none") +
  labs(x = "Равенство", y = "Ангажираност на заинтересованите страни")

# ggsave(
#   "ncp-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 22,
#   height = 14
# )

gp |>
  dplyr::select(48:54) |>
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
    Parameter1 =
      case_when(
        Parameter1 == "ncp_funding_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
        Parameter1 == "ncp_funding_other_industry" ~ "Бизнес",
        Parameter1 == "ncp_funding_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
        Parameter1 == "ncp_funding_private_household_out_of_pocket_expenditure" ~ "Лични разходи",
        Parameter1 == "ncp_funding_private_voluntary_health_insurance_funding" ~ "Доброволни ЗОФ",
        Parameter1 == "ncp_funding_public_goverment_funding" ~ "Държавно финансиране",
        Parameter1 == "ncp_funding_public_health_insurance_funding" ~ "Задължителни ЗОФ"
      ),
    Parameter2 =
          case_when(
            Parameter2 == "ncp_funding_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
            Parameter2 == "ncp_funding_other_industry" ~ "Бизнес",
            Parameter2 == "ncp_funding_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
            Parameter2 == "ncp_funding_private_household_out_of_pocket_expenditure" ~ "Лични разходи",
            Parameter2 == "ncp_funding_private_voluntary_health_insurance_funding" ~ "Доброволни ЗОФ",
            Parameter2 == "ncp_funding_public_goverment_funding" ~ "Държавно финансиране",
            Parameter2 == "ncp_funding_public_health_insurance_funding" ~ "Задължителни ЗОФ"
      ),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 45, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "", subtitle = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))

#ggsave(
#  "ncp-cor-finance-bg.png",
#  bg = "white",
#  units = "cm",
#  dpi = 1000,
#  width = 22,
#  height = 14
#)

ncp_total <-
  eu |>
  dplyr::select(5:13, 15:21, 23:51, 173, 174) |>
  rowwise() %>%
  mutate(# Use c_across to select the columns and sum them
    ncpsum = sum(c_across(starts_with("ncp_")))) |>
  ungroup()

ncp_total |>
  mutate(country = as.factor(country)) |>
  mutate(
    country = case_when(
      country == "Croatia" ~ "Хърватия",
      country == "Cyprus" ~ "Кипър",
      country == "Czech Republic" ~ "Чехия",
      country == "Denmark" ~ "Дания",
      country == "Finland" ~ "Финландия",
      country == "France" ~ "Франция",
      country == "Germany" ~ "Германия",
      country == "Greece" ~ "Гърция",
      country == "Ireland" ~ "Ирландия",
      country == "Italy" ~ "Италия",
      country == "Austria" ~ "Австрия",
      country == "Latvia" ~ "Латвия",
      country == "Lithuania" ~ "Литва",
      country == "Netherlands" ~ "Холандия",
      country == "Norway" ~ "Норвегия",
      country == "Poland" ~ "Полша",
      country == "Portugal" ~ "Португалия",
      country == "Slovakia" ~ "Словакия",
      country == "Slovenia" ~ "Словения",
      country == "Spain" ~ "Испания",
      country == "UK" ~ "Великобритания",
      country == "Belgium" ~ "Белгия",
      country == "Bulgaria" ~ "България",
      country == "Estonia" ~ "Естония",
      country == "Hungary" ~ "Унгария",
      country == "Malta" ~ "Малта",
      country == "Sweden" ~ "Швеция",
      country == "Switzerland" ~ "Швейцария"
    ),
  ) |>
  aov(ncpsum ~ country, data = _) |>
  emmeans::emmeans(specs = "country") |>
  pairs(adjust = "bonferroni") |>
  tidy() |>
  dplyr::select(2, 4, 5, 7, 8) |>
  filter(adj.p.value < 0.05) |>
  mutate(
    lower = estimate - 1.96 * std.error,
    upper = estimate + 1.96 * std.error,
    CI = paste0("[", round(lower, 2), ", ", round(upper, 2), "]"),
    pv = case_when(adj.p.value > 0.9 ~ ">0.9", TRUE ~ as.character(round(adj.p.value, 3)))
  ) |>
  mutate_if(is.numeric, round, 2) |>
  dplyr::select(1, 2, 4, 8, 9)


ncp_total |>
  dplyr::select(-c(country, 38:45)) |>
  lm(ncpsum ~ ., data = _) |>
  tidy(round(2))

tree_dat <-
  ncp_total |>
  dplyr::select(-c(country, 38:45)) |>
  rename("Age" = age,
         "HCEPC" = hcepc,
         "RC experience" = cancer_exp_years,)


tree_spec <-
  decision_tree(mode = "regression")  |>
  set_engine("rpart", model = TRUE)

tree_spec <-
  tree_spec %>%
  fit(ncpsum ~ ., data = tree_dat)



extract_fit_engine(tree_spec) |>
  rpart.plot::rpart.plot()


ncp_total |>
  dplyr::select(-c(country, 38:45)) |>
  mutate(hcepc_1883 = ifelse(hcepc > 1883, 1, 0)) |>
  aov(ncpsum ~ hcepc_1883, data = _) |>
  emmeans::emmeans(specs = "hcepc_1883") |>
  pairs(adjust = "bonferroni")



ncp_total |>
  dplyr::select(-c(country, 38:45)) |>
  mutate(hcepc_1883 = ifelse(hcepc > 1883, 1, 0)) |>
  filter(hcepc_1883 == 0) |>
  mutate(age_58 = ifelse(age < 58, 0, 1)) |>
  aov(ncpsum ~ age_58, data = _) |>
  emmeans::emmeans(specs = "age_58") |>
  pairs(adjust = "bonferroni")


ncp_total |>
  dplyr::select(-c(country, 38:45)) |>
  mutate(hcepc_1883 = ifelse(hcepc > 1883, 1, 0)) |>
  filter(hcepc_1883 == 1) |>
  mutate(hcepc_4530 = ifelse(hcepc > 4530, 1, 0)) |>
  aov(ncpsum ~ hcepc_4530, data = _) |>
  emmeans::emmeans(specs = "hcepc_4530") |>
  pairs(adjust = "bonferroni")


ncp_total |>
  dplyr::select(-c(country, 38:45)) |>
  mutate(hcepc_1883 = ifelse(hcepc > 1883, 1, 0)) |>
  filter(hcepc_1883 == 1) |>
  mutate(hcepc_4530 = ifelse(hcepc > 4530, 1, 0)) |>
  filter(hcepc_4530 == 1) |>
  mutate(hcepc_5237 = ifelse(hcepc > 5237, 1, 0)) |>
  aov(ncpsum ~ hcepc_5237, data = _) |>
  emmeans::emmeans(specs = "hcepc_5237") |>
  pairs(adjust = "bonferroni")


ncp_total |>
  dplyr::select(-c(country, 38:45)) |>
  mutate(hcepc_1883 = ifelse(hcepc > 1883, 1, 0)) |>
  filter(hcepc_1883 == 1) |>
  mutate(hcepc_4530 = ifelse(hcepc > 4530, 1, 0)) |>
  filter(hcepc_4530 == 0) |>
  mutate(rc_11 = ifelse(cancer_exp_years > 11, 1, 0)) |>
  aov(ncpsum ~ rc_11, data = _) |>
  emmeans::emmeans(specs = "rc_11") |>
  pairs(adjust = "bonferroni")



ncp_total |>
  dplyr::select(-c(country, 38:45)) |>
  mutate(hcepc_1883 = ifelse(hcepc > 1883, 1, 0)) |>
  filter(hcepc_1883 == 1) |>
  mutate(hcepc_4530 = ifelse(hcepc > 4530, 1, 0)) |>
  filter(hcepc_4530 == 0) |>
  mutate(rc_11 = ifelse(cancer_exp_years > 11, 1, 0)) |>
  filter(rc_11 == 1) |>
  mutate(age49 = ifelse(age < 49, 0, 1)) |>
  aov(ncpsum ~ age49, data = _) |>
  emmeans::emmeans(specs = "age49") |>
  pairs(adjust = "bonferroni")

ncp_total |>
  dplyr::select(-c(country, 38:45)) |>
  aov(ncpsum ~ ., data = _) |>
  marginaleffects::avg_predictions()


gp |>
  dplyr::select(48:54) |>
  pivot_longer(cols = 1:7,
               names_to = "variable",
               values_to = "value") |>
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(specs = "variable") |>
  tidy() |>
  ggplot(aes(x = estimate, y = fct_reorder(variable, estimate))) +
  geom_point(aes(color = variable), size = 3) +
  geom_rangeframe(data = tibble(
    variable = c(
      "ncp_funding_other_eu_financing_project_lines",
      "ncp_funding_other_industry",
      "ncp_funding_other_non_profit_institutions_serving_households",
      "ncp_funding_private_household_out_of_pocket_expenditure",
      "ncp_funding_private_voluntary_health_insurance_funding",
      "ncp_funding_public_goverment_funding",
      "ncp_funding_public_health_insurance_funding"
    ),
    estimate = c(1, 5, 1, 1, 1, 1, 1)
  )) +
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.2f", estimate
    ))),
    hjust = +0.5,
    vjust = -0.5,
    size = 5,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  geom_errorbar(
    aes(
      xmin = estimate - 1.96 * std.error,
      xmax = estimate + 1.96 * std.error,
      colour = variable
    ),
    width = 0.2,
    alpha = 0.7,
    size = 0.5,
  ) +
  geom_vline(
    xintercept = 2.77,
    lty = 2,
    size = 0.5,
    color = "gray10"
  ) +
  scale_y_discrete(
    labels = c(
      "ncp_funding_other_eu_financing_project_lines" = "Програми и фондове на ЕС",
      "ncp_funding_other_industry" = "Бизнес",
      "ncp_funding_other_non_profit_institutions_serving_households" = "Финансиране от НПО",
      "ncp_funding_private_household_out_of_pocket_expenditure" = "Лични разходи",
      "ncp_funding_private_voluntary_health_insurance_funding" = "Доброволни ЗОФ",
      "ncp_funding_public_goverment_funding" = "Държавно финансиране",
      "ncp_funding_public_health_insurance_funding" = "Задължителни ЗОФ"
    )
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(1, 5.5),
    breaks = c(seq(1, 5, 1))
  ) +
  theme(legend.position = "none") +
  scale_color_manual(values = c(
    "#03346E",
    "#03346E",
    "#03346E",
    "#973131",
    "#973131",
    "#059212",
    "#059212"
  )) +
  labs(x = "", y = "", subtitle = "")

# ggsave(
#   "mean-finance-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 24,
#   height = 12
# )


gp |>
  dplyr::select(48:54) |>
  pivot_longer(cols = 1:7,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    variable = case_when(
      variable == "ncp_funding_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
      variable == "ncp_funding_other_industry" ~ "Бизнес",
      variable == "ncp_funding_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
      variable == "ncp_funding_private_household_out_of_pocket_expenditure" ~ "Лични разходи",
      variable == "ncp_funding_private_voluntary_health_insurance_funding" ~ "Доброволни ЗОФ",
      variable == "ncp_funding_public_goverment_funding" ~ "Държавно финансиране",
      variable == "ncp_funding_public_health_insurance_funding" ~ "Задължителни ЗОФ"
    )
  ) |>
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(specs = "variable") |>
  pairs(adjust = "bonferroni") |>
  tidy() |>
  dplyr::select(2, 4, 5, 7, 8) |>
  mutate_if(is.numeric, round, 2) |>
  mutate(
    lower = estimate - 1.96 * std.error,
    upper = estimate + 1.96 * std.error,
    "95%CI" = paste0("[", round(lower, 2), ", ", round(upper, 2), "]"),
    p = case_when(
      adj.p.value > 0.9 ~ ">0.9",
      adj.p.value < 0.001 ~ "<0.01",
      TRUE ~ as.character(round(adj.p.value, 3))
    )
  ) |>
  dplyr::select(1, 2, 4, 8, 9)


gp |>
  dplyr::select(48:54) |>
  correlation() |>
  tibble() |>
  mutate(
    Parameter1 = case_when(
      Parameter1 == "ncp_funding_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
      Parameter1 == "ncp_funding_other_industry" ~ "Бизнес",
      Parameter1 == "ncp_funding_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
      Parameter1 == "ncp_funding_private_household_out_of_pocket_expenditure" ~ "Лични разходи",
      Parameter1 == "ncp_funding_private_voluntary_health_insurance_funding" ~ "Доброволни ЗОФ",
      Parameter1 == "ncp_funding_public_goverment_funding" ~ "Държавно финансиране",
      Parameter1 == "ncp_funding_public_health_insurance_funding" ~ "Задължителни ЗОФ"
    ),
    Parameter2 = case_when(
      Parameter2 == "ncp_funding_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
      Parameter2 == "ncp_funding_other_industry" ~ "Бизнес",
      Parameter2 == "ncp_funding_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
      Parameter2 == "ncp_funding_private_household_out_of_pocket_expenditure" ~ "Лични разходи",
      Parameter2 == "ncp_funding_private_voluntary_health_insurance_funding" ~ "Доброволни ЗОФ",
      Parameter2 == "ncp_funding_public_goverment_funding" ~ "Държавно финансиране",
      Parameter2 == "ncp_funding_public_health_insurance_funding" ~ "Задължителни ЗОФ"
    )
  ) |>
  mutate_if(is.numeric, round, 2) |>
  mutate(CI = paste0("[", CI_low, ", ", CI_high, "]")) |>
  dplyr::select(Parameter1, Parameter2, r, CI, p) |>
  mutate(p = case_when(p > 0.9 ~ ">0.9", p < 0.001 ~ "<0.01", TRUE ~ as.character(round(p, 3))))


gp |>
  count(
    ncp_funding_private_voluntary_health_insurance_funding,
    ncp_funding_private_household_out_of_pocket_expenditure
  ) |>
  full_join(
    expand.grid(
      ncp_funding_private_voluntary_health_insurance_funding = 1:5,
      ncp_funding_private_household_out_of_pocket_expenditure = 1:5
    )
  ) |>
  mutate(n = ifelse(is.na(n), 0, n),
         sum = sum(n),
         prop = n / sum) |>
  ggplot(
    aes(x = ncp_funding_private_voluntary_health_insurance_funding, y = ncp_funding_private_household_out_of_pocket_expenditure)
  ) +
  geom_tile(
    aes(fill = prop),
    color = "white",
    alpha = 0.9,
    linewidth = 1
  ) +
  geom_text(
    aes(label = ifelse(prop > 0,
                       paste0("  ", sprintf(
                         "%2.1f", prop * 100
                       ), "%  "),
                       ""
    )),
    vjust = 0.5,
    hjust = 0.5,
    size = 5,
    family = "Roboto Condensed",
  )+
  geom_rangeframe(
    data = tibble(
      ncp_funding_private_voluntary_health_insurance_funding = c(1, 2, 3, 4, 5),
      ncp_funding_private_household_out_of_pocket_expenditure = c(1, 2, 3, 4, 5)
    ),
  ) +
  scale_fill_gradient2(
    midpoint = 0.40,
    low = "white",
    mid = "#31B1C2",
    high = "#021526"
  ) +
  theme(legend.position = "none") +
  labs(x = "Доброволни ЗОФ", y = "Лични разходи")

# ggsave(
#   "ncp-fund-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 22,
#   height = 14
# )



gp |>
  dplyr::select(48:54) |>
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
    Parameter1 = case_when(
      Parameter1 == "ncp_funding_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
      Parameter1 == "ncp_funding_other_industry" ~ "Бизнес",
      Parameter1 == "ncp_funding_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
      Parameter1 == "ncp_funding_private_household_out_of_pocket_expenditure" ~ "Лични разходи",
      Parameter1 == "ncp_funding_private_voluntary_health_insurance_funding" ~ "Доброволни ЗОФ",
      Parameter1 == "ncp_funding_public_goverment_funding" ~ "Държавно финансиране",
      Parameter1 == "ncp_funding_public_health_insurance_funding" ~ "Задължителни ЗОФ"
    ),
    Parameter2 = case_when(
      Parameter2 == "ncp_funding_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
      Parameter2 == "ncp_funding_other_industry" ~ "Бизнес",
      Parameter2 == "ncp_funding_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
      Parameter2 == "ncp_funding_private_household_out_of_pocket_expenditure" ~ "Лични разходи",
      Parameter2 == "ncp_funding_private_voluntary_health_insurance_funding" ~ "Доброволни ЗОФ",
      Parameter2 == "ncp_funding_public_goverment_funding" ~ "Държавно финансиране",
      Parameter2 == "ncp_funding_public_health_insurance_funding" ~ "Задължителни ЗОФ"
    ),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |> 
  tibble() |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 45, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "", subtitle = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))

# ggsave(
#   "ncp-full-fund-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 22,
#   height = 14
# )


gp |>
  dplyr::select(48:54) |>
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
    Parameter1 = case_when(
      Parameter1 == "ncp_funding_other_eu_financing_project_lines" ~ "EU financing project lines",
      Parameter1 == "ncp_funding_other_industry" ~ "Industry",
      Parameter1 == "ncp_funding_other_non_profit_institutions_serving_households" ~ "Non profit institutions",
      Parameter1 == "ncp_funding_private_household_out_of_pocket_expenditure" ~ "Out of pocket",
      Parameter1 == "ncp_funding_private_voluntary_health_insurance_funding" ~ "Voluntary health insurance",
      Parameter1 == "ncp_funding_public_goverment_funding" ~ "Government funding",
      Parameter1 == "ncp_funding_public_health_insurance_funding" ~ "Universal health insurance"),
    Parameter2 = case_when(
      Parameter2 == "ncp_funding_other_eu_financing_project_lines" ~ "EU financing project lines",
      Parameter2 == "ncp_funding_other_industry" ~ "Industry",
      Parameter2 == "ncp_funding_other_non_profit_institutions_serving_households" ~ "Non profit institutions",
      Parameter2 == "ncp_funding_private_household_out_of_pocket_expenditure" ~ "Out of pocket",
      Parameter2 == "ncp_funding_private_voluntary_health_insurance_funding" ~ "Voluntary health insurance",
      Parameter2 == "ncp_funding_public_goverment_funding" ~ "Government funding",
      Parameter2 == "ncp_funding_public_health_insurance_funding" ~ "Universal health insurance"
    ),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |> 
  tibble() |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 45, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "", subtitle = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))

 ggsave(
   "ncp-full-fund-cor-en.png",
   bg = "white",
   units = "cm",
   dpi = 1000,
   width = 22,
   height = 14
 )


gp |>
  mutate(id = row_number()) |>
  left_join(ncp_total |>
              mutate(id = row_number()) |>
              dplyr::select(id, ncpsum), by = "id") |>
  dplyr::select(48:54, ncpsum) |>
  correlation() |>
  tibble() |>
  filter(Parameter2 == "ncpsum")

gp |>
  dplyr::select(1, 3, 4, 48:54) |>
  mutate(id = row_number()) |>
  left_join(ncp_total |>
              mutate(id = row_number()) |>
              dplyr::select(id, ncpsum), by = "id") |>
  dplyr::select(-id) |>
  correlation(
    select = c("age", "cancer_exp_years", "ncpsum"),
    select2 = c(
      "ncp_funding_public_health_insurance_funding",
      "ncp_funding_private_voluntary_health_insurance_funding",
      "ncp_funding_private_household_out_of_pocket_expenditure",
      "ncp_funding_other_non_profit_institutions_serving_households",
      "ncp_funding_other_eu_financing_project_lines",
      "ncp_funding_other_industry"
    )
  ) |>
  tibble()


gp |>
  dplyr::select(2, 48:54) |>
  pivot_longer(cols = 2:8,
               names_to = "variable",
               values_to = "value") |>
  aov(value ~ variable + country, data = _)


gp |>
  dplyr::select(2, 48:54) |>
  pivot_longer(cols = 2:8,
               names_to = "variable",
               values_to = "value") |>
  group_by(country, variable) |>
  summarise(
    n = n(),
    mean = mean(value, na.rm = TRUE),
    sd = sd(value, na.rm = TRUE)
  ) |>
  mutate_if(is.numeric, round, 2) |>
  mutate(
    variable = case_when(
      variable == "ncp_funding_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
      variable == "ncp_funding_other_industry" ~ "Бизнес",
      variable == "ncp_funding_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
      variable == "ncp_funding_private_household_out_of_pocket_expenditure" ~ "Лични разходи",
      variable == "ncp_funding_private_voluntary_health_insurance_funding" ~ "Доброволни ЗОФ",
      variable == "ncp_funding_public_goverment_funding" ~ "Държавно финансиране",
      variable == "ncp_funding_public_health_insurance_funding" ~ "Задължителни ЗОФ"
    ),
    country = case_when(
      country == "Croatia" ~ "Хърватия",
      country == "Cyprus" ~ "Кипър",
      country == "Czech Republic" ~ "Чехия",
      country == "Denmark" ~ "Дания",
      country == "Finland" ~ "Финландия",
      country == "France" ~ "Франция",
      country == "Germany" ~ "Германия",
      country == "Greece" ~ "Гърция",
      country == "Ireland" ~ "Ирландия",
      country == "Italy" ~ "Италия",
      country == "Austria" ~ "Австрия",
      country == "Latvia" ~ "Латвия",
      country == "Lithuania" ~ "Литва",
      country == "Netherlands" ~ "Холандия",
      country == "Norway" ~ "Норвегия",
      country == "Poland" ~ "Полша",
      country == "Portugal" ~ "Португалия",
      country == "Slovakia" ~ "Словакия",
      country == "Slovenia" ~ "Словения",
      country == "Spain" ~ "Испания",
      country == "UK" ~ "Великобритания",
      country == "Belgium" ~ "Белгия",
      country == "Bulgaria" ~ "България",
      country == "Estonia" ~ "Естония",
      country == "Hungary" ~ "Унгария",
      country == "Malta" ~ "Малта",
      country == "Sweden" ~ "Швеция",
      country == "Switzerland" ~ "Швейцария"
    )
  ) |>
  dplyr::select(country, n, variable, mean, sd)


gp |>
  dplyr::select(2, 48:54) |>
  pivot_longer(cols = 2:8,
               names_to = "variable",
               values_to = "value") |>
  aov(value ~ variable + country, data = _) |>
  emmeans::emmeans(specs = c("variable", "country"))


gp |>
  dplyr::select(-c(2, 10, 18, 40:47, 55))


funding_models <-
  gp |>
  dplyr::select(-c(2, 10, 18, 40:47, 55)) |>
  pivot_longer(cols = 37:43,
               names_to = "variable",
               values_to = "value") |>
  group_by(variable) |>
  nest() |>
  mutate(
    models = map(data, ~ lm(value ~ ., data = .x)),
    comparions = map(
      models,
      ~ marginaleffects::avg_comparisons(.x, p_adjust = "bonferroni")
    )
  ) |>
  unnest(comparions) |>
  dplyr::select("variable", "term", "contrast", "estimate", "p.value") |>
  mutate_if(is.numeric, round, 2) |>
  mutate(p = case_when(
    p.value > 0.9 ~ ">0.9",
    p.value < 0.05 ~ "<0.05",
    TRUE ~ as.character(round(p.value, 3))
  ))


funding_models |>
  mutate(
    variable = case_when(
      variable == "ncp_funding_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
      variable == "ncp_funding_other_industry" ~ "Бизнес",
      variable == "ncp_funding_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
      variable == "ncp_funding_private_household_out_of_pocket_expenditure" ~ "Лични разходи",
      variable == "ncp_funding_private_voluntary_health_insurance_funding" ~ "Доброволни ЗОФ",
      variable == "ncp_funding_public_goverment_funding" ~ "Държавно финансиране",
      variable == "ncp_funding_public_health_insurance_funding" ~ "Задължителни ЗОФ"
    )
  ) |>
  dplyr::select(-p.value)

gp |>
  mutate(id = row_number()) |>
  left_join(ncp_total |>
              mutate(id = row_number()) |>
              dplyr::select(id, ncpsum), by = "id") |>
  dplyr::select(-id) |>
  dplyr::select(ncpsum, 48:54) |>
  pivot_longer(cols = 2:8,
               names_to = "variable",
               values_to = "value") |>
  group_by(variable) |>
  correlation() |>
  tibble() |>
  mutate_if(is.numeric, round, 2) |>
  dplyr::select(Group, Parameter1, Parameter2, r, CI_low, CI_high, p) |>
  mutate(
    Parameter1 = case_when(
      Group == "ncp_funding_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
      Group == "ncp_funding_other_industry" ~ "Бизнес",
      Group == "ncp_funding_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
      Group == "ncp_funding_private_household_out_of_pocket_expenditure" ~ "Лични разходи",
      Group == "ncp_funding_private_voluntary_health_insurance_funding" ~ "Доброволни ЗОФ",
      Group == "ncp_funding_public_goverment_funding" ~ "Държавно финансиране",
      Group == "ncp_funding_public_health_insurance_funding" ~ "Задължителни ЗОФ"
    ),
    Parameter2 = case_when(Parameter2 == "value" ~ "ПРЗГН", TRUE ~ "error"),
    "95CI" = paste0("[", CI_low, ", ", CI_high, "]"),
    p = case_when(p > 0.9 ~ ">0.9", p < 0.001 ~ "<0.01", TRUE ~ as.character(round(p, 3)))
  ) |>
  dplyr::select(Parameter1, Parameter2, r, "95CI", p)

final_kmeans <- gp |>
  dplyr::select(48:54) |>
  kmeans(centers = 2)

results <- augment(final_kmeans, gp)

# results |>
#   mutate(.cluster = as.numeric(.cluster),
#          hcepc_hight = as.numeric(hcepc_hight)) |>
#   dplyr::select(-c(2, 10,18,40:47, 55)) |>
#   convert_to_dummmy() |>
#   gtsummary::tbl_summary(by = .cluster,
#                          type = list(
#   "ncp_funding_public_goverment_funding" ~ "continuous",
#   "ncp_funding_public_health_insurance_funding" ~ "continuous",
#   "ncp_funding_private_voluntary_health_insurance_funding" ~ "continuous",
#   "ncp_funding_private_household_out_of_pocket_expenditure" ~ "continuous",
#   "ncp_funding_other_non_profit_institutions_serving_households" ~ "continuous",
#   "ncp_funding_other_industry" ~ "continuous",
#   "ncp_funding_other_eu_financing_project_lines" ~ "continuous"),
#   statistic = list(all_continuous() ~ "{mean} ({sd})"),
#   digits = list(age = c(0, 1))) |>
#   add_difference() |>
#   as_flex_table()



gp |>
  col_n_sum(55) |>
  pcit() |>
  compare_proportions()


gp |>
  dplyr::select(55) |>
  table() |>
  rstatix::chisq_test()

# gp |>
#   dplyr::select(-c(2,10,18,40:54,55)) |>
#   mutate(hcepc_hight = as.numeric(hcepc_hight),
#          rowid = row_number()) |>
#   convert_to_dummmy() |>
#   left_join(gp |>
#               mutate(rowid = row_number()) |>
#               dplyr::select(approaches_for_rare_cancer_policies, rowid)) |>
#   dplyr::select(-rowid) |>
#   gtsummary::tbl_summary(
#     by = approaches_for_rare_cancer_policies
#   ) |>
#   add_p() |>
#   as_flex_table()




gp |>
  count(approaches_for_rare_cancer_policies, ern_none) |>
  group_by(approaches_for_rare_cancer_policies) |>
  mutate(sum = sum(n), ern_none = as_factor(ern_none)) |>
  pcit() |>
  mutate(
    approaches_for_rare_cancer_policies = case_when(
      approaches_for_rare_cancer_policies == "Aligning rare cancer policies with all other cancer-related policies" ~ "onko",
      approaches_for_rare_cancer_policies == "Aligning rare cancer policies with other policies related to rare diseases" ~ "rd",
      approaches_for_rare_cancer_policies == "Establishing rare cancer policies as a distinct area of policies" ~ "separate"
    )
  ) |>
  compare_proportions()

gp |>
  count(
    area_of_rare_cancers_head_and_neck_rare_cancers,
    approaches_for_rare_cancer_policies,
  ) |>
  group_by(area_of_rare_cancers_head_and_neck_rare_cancers) |>
  mutate(
    sum = sum(n),
    area_of_rare_cancers_head_and_neck_rare_cancers = as_factor(area_of_rare_cancers_head_and_neck_rare_cancers)
  ) |>
  pcit() |>
  compare_proportions_by()

## Prevention policies##

pp <-
  eu |>
  dplyr::select(5:13, 15:21, 23:100, 173, 174) |>
  rowwise() |>
  mutate(ncpsum = sum(c_across(38:45), na.rm = TRUE)) |>
  ungroup() |>
  dplyr::select(-c(38:45)) |>
  rename_with(
    ~ gsub("^cancer_prevention_policies_", "cpv_", .),
    starts_with("cancer_prevention_policies_")
  ) |>
  rename_with(
    ~ gsub("^sources_for_screening_programs_", "scrfund_", .),
    starts_with("sources_for_screening_programs_")
  ) |>
  rename_with( ~ gsub("^implementation_", "imp_", .),
               starts_with("implementation_")) |>
  rename_with(
    ~ gsub("^eu_cancer_plan_recommendations_", "eucbp_", .),
    starts_with("eu_cancer_plan_recommendations_")
  )





pp |>
  dplyr::select(46:51) |>
  get_summary_stats() |>
  ggplot(aes(x = mean, y = fct_reorder(variable, mean))) +
  geom_point(size = 3) +
  geom_rangeframe(data = tibble(
    variable = c(
      "cpv_knowledge",
      "cpv_perception",
      "cpv_attitude",
      "cpv_communication",
      "cpv_reach",
      "cpv_impact"
    ),
    mean = c(1, 5, 1, 1, 1, 1)
  )) +
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.2f", mean
    ))),
    hjust = +0.5,
    vjust = -0.5,
    size = 5,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  geom_errorbar(
    aes(xmin = mean - 1.96 * se, xmax = mean + 1.96 * se),
    width = 0.2,
    size = 0.5,
    color = "gray10"
  ) +
  geom_vline(
    xintercept = 2.76,
    lty = 2,
    size = 0.5,
    color = "gray10"
  ) +
  scale_y_discrete(
    labels = c(
      "cpv_knowledge" = "Информираност",
      "cpv_perception" = "Възприятие",
      "cpv_attitude" = "Отношение",
      "cpv_communication" = "Комуникация",
      "cpv_reach" = "Обхват",
      "cpv_impact" = "Влияние"
    )
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(1, 5.5),
    breaks = c(seq(1, 5, 1))
  ) +
  labs(x = "", y = "", subtitle = "")

# ggsave(
#   "mean-prevention-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 24,
#   height = 12
# )


pp_models <-
  pp |>
  rowwise() |>
  mutate(cvpsum = sum(
    c(
      cpv_knowledge,
      cpv_perception,
      cpv_attitude,
      cpv_communication,
      cpv_reach,
      cpv_impact
    ),
    na.rm = TRUE
  )) |>
  dplyr::select(-c("country" , starts_with("cpv_"))) |>
  dplyr::select(-c(45:79)) |>
  univariate_predictors(outcome_var = "cvpsum") |>
  mutate_if(is.numeric, round, 2)

pp_models |>
  filter(p_lm_value < 0.05)

pp |>
  dplyr::select(46:51) |>
  correlation() |>
  tibble()


pp |>
  count(cpv_reach, cpv_communication) |>
  full_join(expand.grid(cpv_communication = 1:5, cpv_reach = 1:5)) |>
  mutate(n = ifelse(is.na(n), 0, n),
         sum = sum(n),
         prop = n / sum) |>
  ggplot(aes(x = cpv_reach, y = cpv_communication)) +
  geom_tile(
    aes(fill = prop),
    color = "white",
    alpha = 0.9,
    linewidth = 1
  ) +
  geom_text(
    aes(label = ifelse(prop > 0,
                       paste0("  ", sprintf(
                         "%2.1f", prop * 100
                       ), "%  "),
                       ""
    )),
    vjust = 0.5,
    hjust = 0.5,
    size = 5,
    family = "Roboto Condensed",
  )+
  geom_rangeframe(data = tibble(
    cpv_reach = c(1, 2, 3, 4, 5),
    cpv_communication = c(1, 2, 3, 4, 5)
  ), ) +
  scale_fill_gradient2(
    midpoint = 0.21,
    low = "white",
    mid = "#31B1C2",
    high = "#021526"
  ) +
  theme(legend.position = "none") +
  labs(x = "Комуникация", y = "Обхват")

# ggsave(
#   "pp-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 22,
#   height = 14
# )

pp |>
  dplyr::select(46:51) |>
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
    Parameter1 =
      case_when(
        Parameter1 == "cpv_knowledge"     ~ "Информираност",
        Parameter1 == "cpv_perception"    ~ "Възприятие",
        Parameter1 == "cpv_attitude"      ~ "Отношение",
        Parameter1 == "cpv_communication" ~ "Комуникация",
        Parameter1 == "cpv_reach"         ~ "Обхват",
        Parameter1 == "cpv_impact"        ~ "Влияние"
      ),
    Parameter2 =
      case_when(
        Parameter2 == "cpv_knowledge"     ~ "Информираност",
        Parameter2 == "cpv_perception"    ~ "Възприятие",
        Parameter2 == "cpv_attitude"      ~ "Отношение",
        Parameter2 == "cpv_communication" ~ "Комуникация",
        Parameter2 == "cpv_reach"         ~ "Обхват",
        Parameter2 == "cpv_impact"        ~ "Влияние"
      ),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 45, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "", subtitle = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))


# ggsave(
#   "pp-ful-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 22,
#   height = 14
# )

pp |>
  dplyr::select(46:51) |>
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
    Parameter1 =
      case_when(
        Parameter1 == "cpv_knowledge"     ~ "Knowledge",
        Parameter1 == "cpv_perception"    ~ "Perception",
        Parameter1 == "cpv_attitude"      ~ "Attitude",
        Parameter1 == "cpv_communication" ~ "Communication",
        Parameter1 == "cpv_reach"         ~ "Reach",
        Parameter1 == "cpv_impact"        ~ "Impact"
      ),
    Parameter2 =
      case_when(
        Parameter2 == "cpv_knowledge"     ~ "Knowledge",
        Parameter2 == "cpv_perception"    ~ "Perception",
        Parameter2 == "cpv_attitude"      ~ "Attitude",
        Parameter2 == "cpv_communication" ~ "Communication",
        Parameter2 == "cpv_reach"         ~ "Reach",
        Parameter2 == "cpv_impact"        ~ "Impact"
      ),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 45, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "", subtitle = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))


# ggsave(
#   "pp-ful-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 22,
#   height = 14
# )

pp |>
  rowwise() |>
  mutate(cvpsum = sum(across(c(46:51)))) |>
  ungroup() |>
  dplyr::select(-c("country" , starts_with("cpv_"))) |>
  dplyr::select(-c(45:80)) |>
  ggplot(aes(x = cvpsum, y = ncpsum)) +
  geom_density_2d(alpha = 0.6, color = "#088395", ) +
  geom_point(color = "gray15",
             alpha = 0.6,
             size = 1.2) +
  geom_rangeframe(data = tibble(cvpsum = c(6, 30), ncpsum = c(8, 40))) +
  geom_rug(
    color = "gray20",
    alpha = 0.6,
    position = "jitter"
  ) +
  geom_smooth(
    method = "lm",
    lty = 2,
    fill = "#36BA98",
    alpha = 0.6,
    size = 0.8,
    color = "gray10"
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(5, 32),
    breaks = c(seq(6, 30, 4))
  ) +
  scale_y_continuous(
    expand = c(0, 0),
    limits = c(7, 45),
    breaks = c(seq(8, 40, 8))
  ) +
  labs(x = "Обща оценка на превантивните политики", y = "Обща оценка на националните ракови планове")

# ggsave(
#    "pp-ncp-bg.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 22,
#    height = 14
#  )




eu_countries |>
  left_join(
    pp |>
      rowwise() |>
      mutate(cvpsum = sum(across(c(
        46:51
      )))) |>
      ungroup() |>
      dplyr::select(-c(starts_with("cpv_"))) |>
      group_by(country) |>
      summarise(mean = mean(cvpsum, na.rm = TRUE))
  ) |>
  ggplot(aes(x = long, y = lat, group = group)) +
  geom_polygon(
    aes(fill = mean),
    alpha = 1.4,
    color = "black",
    lty = 1,
    linewidth = 0.2
  ) +
  theme_void() +
  theme(legend.position = "none") +
  scale_fill_gradient2(
    midpoint = 16.5,
    low = "#FFC96F",
    mid = "#68D2E8",
    high = "#003285"
  )

#  ggsave(
#    "eu-pp-map.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 11,
#    height = 11
#  )

pp |>
  rowwise() |>
  mutate(cvpsum = sum(across(c(46:51)))) |>
  ungroup() |>
  dplyr::select(-c(starts_with("cpv_"))) |>
  group_by(country) |>
  summarise(
    n = n(),
    mean = mean(cvpsum, na.rm = TRUE),
    SE = sd(cvpsum, na.rm = TRUE) / sqrt(n()),
    lower = mean - 1.96 * SE,
    upper = mean + 1.96 * SE,
    "95%CI" = paste0("[", round(lower, 2), ", ", round(upper, 2), "]")
  ) |>
  dplyr::select(country, n, mean, "95%CI") |>
  mutate(
    country = case_when(
      country == "Croatia" ~ "Хърватия",
      country == "Cyprus" ~ "Кипър",
      country == "Czech Republic" ~ "Чехия",
      country == "Denmark" ~ "Дания",
      country == "Finland" ~ "Финландия",
      country == "France" ~ "Франция",
      country == "Germany" ~ "Германия",
      country == "Greece" ~ "Гърция",
      country == "Ireland" ~ "Ирландия",
      country == "Italy" ~ "Италия",
      country == "Austria" ~ "Австрия",
      country == "Latvia" ~ "Латвия",
      country == "Lithuania" ~ "Литва",
      country == "Netherlands" ~ "Холандия",
      country == "Norway" ~ "Норвегия",
      country == "Poland" ~ "Полша",
      country == "Portugal" ~ "Португалия",
      country == "Slovakia" ~ "Словакия",
      country == "Slovenia" ~ "Словения",
      country == "Spain" ~ "Испания",
      country == "UK" ~ "Великобритания",
      country == "Belgium" ~ "Белгия",
      country == "Bulgaria" ~ "България",
      country == "Estonia" ~ "Естония",
      country == "Hungary" ~ "Унгария",
      country == "Malta" ~ "Малта",
      country == "Sweden" ~ "Швеция",
      country == "Switzerland" ~ "Швейцария"
    )
  ) |>
  mutate_if(is.numeric, round, 2) |>
  knitr::kable()

pp_models |>
  dplyr::select(1, 12, 2, 3, 4) |>
  mutate(
    lower = estimate  - 1.96 * std.error,
    upper = estimate  + 1.96 * std.error,
    "95%CI" = paste0("[", round(lower, 2), ", ", round(upper, 2), "]")
  ) |> dplyr::select(-std.error) |>
  mutate_if(is.numeric, round, 2) |>
  flextable::flextable()



pp |>
  dplyr::select(46:51) |>
  pivot_longer(cols = 1:6,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    fct_var = case_when(
      value == 1 ~ "no",
      value == 2 ~ "no",
      value == 3 ~ "both",
      value == 4 ~ "yes",
      value == 5 ~ "yes"
    )
  ) |>
  count(variable, fct_var) |>
  group_by(variable) |>
  pivot_wider(names_from = fct_var, values_from = n) |>
  mutate(
    agreement = (yes + 0.5 * both) / 92,
    disagreement = (no + 0.5 * both) / 92,
    adr = agreement / disagreement,
    adr1 = ifelse(adr > 1, TRUE, FALSE)
  ) |>
  dplyr::select(variable, agreement, disagreement, adr, adr1) |>
  ggplot(aes(
    x = agreement,
    y = fct_reorder(variable, agreement),
    fill = adr1
  )) +
  geom_col(color = "gray10", alpha = 0.7) +
  geom_vline(
    xintercept = 0.5,
    lty = 2,
    size = 0.5,
    color = "#013440"
  ) +
  geom_rangeframe(data = tibble(
    variable = c(
      "cpv_attitude",
      "cpv_communication",
      "cpv_impact",
      "cpv_knowledge",
      "cpv_perception",
      "cpv_reach"
    ),
    agreement = c(0, 1, 0, 0, 0, 0),
    adr1 = c(FALSE, TRUE, FALSE, FALSE, FALSE, FALSE)
  )) +
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.1f", agreement * 100
    ), "%  ")),
    #color = agreement > .05
    #hjust = agreement > .05),
    hjust = "right",
    size = 5,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  scale_fill_manual(values = c("gray85", "#37B7C3")) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(-0.05, 1.1),
    breaks = c(seq(0, 1, 0.2)),
    labels = scales::label_percent()
  ) +
  scale_y_discrete(
    labels = c(
      "cpv_knowledge" = "Информираност",
      "cpv_perception" = "Възприятие",
      "cpv_attitude" = "Отношение",
      "cpv_communication" = "Комуникация",
      "cpv_reach" = "Обхват",
      "cpv_impact" = "Влияние"
    )
  ) +
  theme(legend.position = "none") +
  labs(y = "", x = "%Одобрение")

# ggsave(
#  "cpv-agr-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 24,
#   height = 12
# )

pp |>
  dplyr::select(46:51) |>
  pivot_longer(cols = 1:6,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    variable = case_when(
      variable == "cpv_knowledge" ~ "Информираност",
      variable == "cpv_perception" ~ "Възприятие",
      variable == "cpv_attitude" ~ "Отношение",
      variable == "cpv_communication" ~ "Комуникация",
      variable == "cpv_reach" ~ "Обхват",
      variable == "cpv_impact" ~ "Влияние"
    )
  ) |>
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(specs = c("variable")) |>
  pairs(adjust = "bonferroni") |>
  tidy() |>
  dplyr::select(2, 4, 5, 7, 8) |>
  mutate_if(is.numeric, round, 2) |>
  knitr::kable()

pp |>
  dplyr::select(46:51) |>
  ltm::cronbach.alpha(standardized = T, CI = T)

pp |>
  dplyr::select(46:51) |>
  psych::alpha()

pp |>
  dplyr::select(46:51) |>
  psych::KMO()

pp |>
  dplyr::select(46:51) |>
  psych::cortest.bartlett()

pp |>
  rowwise() |>
  mutate(cvpsum = sum(across(c(46:51)))) |>
  ungroup() |>
  dplyr::select(-c(starts_with("cpv_"))) |>
  dlookr::normality(cvpsum)


pp |>
  rowwise() |>
  mutate(cvpsum = sum(across(c(46:51)))) |>
  ungroup() |>
  dplyr::select(-c(starts_with("cpv_"))) |>
  dlookr::univar_numeric(cvpsum)



#  # run stepwise selection !
#
#  opt_mod_backn <- step(full_model, direction = "backward",
#                      scope = list(upper = full_model, lower = #  null_model))
#
#  opt_mod_forw <- step(null_model, direction = "foward",
#                      scope = list(upper = full_model, lower = #  null_model))
#


# models <-
#   pp|>
#     rowwise() |>
#     mutate(
#       cvpsum = sum(c(cpv_knowledge, cpv_perception, # cpv_attitude, cpv_communication, cpv_reach, cpv_impact), na.rm # = TRUE)
#     ) |>
#     dplyr::select(-c("country" , starts_with("cpv_"))) |>
#     dplyr::select(-c(45:79)) |>
#   dplyr::select(1,2,4,5:14,16:28,29,34,27,35,44,45,48) |>
#     glmulti::glmulti(cvpsum ~ .,
#           data = _,
#           method = "g",
#           crit = aicc, # corrected-AIC > small samples
#           level = 1, # 1 without interactions, 2 with
#           family = gaussian,
#           fitfunction = lm,
#           confsetsize = 100)
#
# print(models)
#
# eval(metafor:::.glmulti)
# # Extract coefficients from the glmulti model
# mmi <- as.data.frame(coef(models, varweighting = "Johnson"))
#
# # Convert the row names to a column
# mmi <- mmi %>%
#   rownames_to_column(var = "Variable") %>%
#   mutate(
#     `Std. Error` = sqrt(`Uncond. variance`),
#     `z value` = Estimate / `Std. Error`,
#     `Pr(>|z|)` = 2 * pnorm(abs(`z value`), lower.tail = FALSE),
#     ci.lb = Estimate - qnorm(0.975) * `Std. Error`,
#     ci.ub = Estimate + qnorm(0.975) * `Std. Error`
#   ) %>%
#   dplyr::select(
#     Variable,
#     Estimate,
#     `Std. Error`,
#     `z value`,
#     ci.lb,
#     ci.ub,
#     `Pr(>|z|)`,
#     Importance
#   ) %>%
#   arrange(desc(Importance)) %>%
#   as_tibble()  # Convert to tibble


pp |>
  rowwise() |>
  mutate(cvpsum = sum(
    c(
      cpv_knowledge,
      cpv_perception,
      cpv_attitude,
      cpv_communication,
      cpv_reach,
      cpv_impact
    ),
    na.rm = TRUE
  )) |>
  dplyr::select(-c("country" , starts_with("cpv_"))) |>
  dplyr::select(-c(45:79)) |>
  dplyr::select(1, 2, 4, 5:14, 16:28, 29, 34, 27, 35, 44, 45, 48) |>
  to_dummmy() |>
  lm(
    cvpsum ~ 1 + workplace_health_authority + area_of_rare_cancers_skin_rare_cancers,
    data = _
  )

pp |>
  dplyr::select(starts_with("ncr_")) |>
  get_summary_stats() |>
  mutate(
    lower = mean - ci,
    upper = mean + ci,
    "95%CI" = paste0("[", round(lower, 2), ", ", round(upper, 2), "]")
  ) |>
  ggplot(aes(x = mean, y = fct_reorder(variable, mean))) +
  geom_point(size = 3) +
  geom_rangeframe(data = tibble(
    variable = c(
      "ncr_completeness",
      "ncr_contemporary",
      "ncr_accuracy",
      "ncr_validity",
      "ncr_representativness",
      "ncr_confidentiality",
      "ncr_patient_outcomes",
      "ncr_influence",
      "ncr_research",
      "ncr_cost_effectivness",
      "ncr_awareness",
      "ncr_collaboration"
    ),
    mean = c(1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)
  )) +
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.2f", mean
    ))),
    hjust = +0.5,
    vjust = -0.5,
    size = 4,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  geom_errorbar(
    aes(xmin = mean - 1.96 * se, xmax = mean + 1.96 * se),
    width = 0.2,
    size = 0.5,
    color = "gray10"
  ) +
  geom_vline(
    xintercept = 3.49,
    lty = 2,
    size = 0.5,
    color = "gray10"
  ) +
  scale_y_discrete(
    labels = c(
      "ncr_completeness"       = "Пълнота",
      "ncr_contemporary"       = "Съвременност",
      "ncr_accuracy"           = "Надеждност",
      "ncr_validity"           = "Валидност",
      "ncr_representativness"  = "Представителност",
      "ncr_confidentiality"    = "Конфиденциалност",
      "ncr_patient_outcomes"   = "Клинично влияние",
      "ncr_influence"          = "Политическо влияние",
      "ncr_research"           = "Изследователско влияние",
      "ncr_cost_effectivness"  = "Разходна ефективност",
      "ncr_awareness"          = "Осведоменост",
      "ncr_collaboration"      = "Сътрудничество"
    )
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(1, 5.5),
    breaks = c(seq(1, 5, 1))
  ) +
  labs(x = "", y = "", subtitle = "")

# ggsave(
#   "mean-ncr-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 20,
#   height = 15
# )

pp |>
  dplyr::select(starts_with("ncr_")) |>
  get_summary_stats() |>
  mutate(
    lower = mean - ci,
    upper = mean + ci,
    "95%CI" = paste0("[", round(lower, 2), ", ", round(upper, 2), "]")
  ) |> 
  dplyr::select(variable, mean, "95%CI") |>
  mutate(
    variable = case_when(
      variable == "ncr_completeness" ~ "Пълнота",
      variable == "ncr_contemporary" ~ "Съвременност",
      variable == "ncr_accuracy" ~ "Надеждност",
      variable == "ncr_validity" ~ "Валидност",
      variable == "ncr_representativness" ~ "Представителност",
      variable == "ncr_confidentiality" ~ "Конфиденциалност",
      variable == "ncr_patient_outcomes" ~ "Клинично влияние",
      variable == "ncr_influence" ~ "Политическо влияние",
      variable == "ncr_research" ~ "Изследователско влияние",
      variable == "ncr_cost_effectivness" ~ "Разходна ефективност",
      variable == "ncr_awareness" ~ "Осведоменост",
      variable == "ncr_collaboration" ~ "Сътрудничество"
    )
  ) |>
  mutate_round() |>
  knitr::kable()



pp |>
  dplyr::select(starts_with("ncr_")) |>
  pivot_longer(cols = 1:12,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    fct_var = case_when(
      value == 1 ~ "no",
      value == 2 ~ "no",
      value == 3 ~ "both",
      value == 4 ~ "yes",
      value == 5 ~ "yes"
    )
  ) |>
  count(variable, fct_var) |>
  group_by(variable) |>
  pivot_wider(names_from = fct_var, values_from = n) |>
  mutate(
    agreement = (yes + 0.5 * both) / 92,
    disagreement = (no + 0.5 * both) / 92,
    adr = agreement / disagreement,
    adr1 = ifelse(adr > 1, TRUE, FALSE)
  ) |>
  dplyr::select(variable, agreement, disagreement, adr, adr1) |>
  ggplot(aes(
    x = agreement,
    y = fct_reorder(variable, agreement),
    fill = adr1
  )) +
  geom_col(color = "gray10", alpha = 0.7) +
  geom_vline(
    xintercept = 0.5,
    lty = 2,
    size = 0.5,
    color = "#013440"
  ) +
  geom_rangeframe(data = tibble(
    variable = c(
      "ncr_completeness",
      "ncr_contemporary",
      "ncr_accuracy",
      "ncr_validity",
      "ncr_representativness",
      "ncr_confidentiality",
      "ncr_patient_outcomes",
      "ncr_influence",
      "ncr_research",
      "ncr_cost_effectivness",
      "ncr_awareness",
      "ncr_collaboration"
    ),
    agreement = c(0, 1, 0, 0, 0, 0,
                  0, 1, 0, 0, 0, 0),
    adr1 = c(FALSE, TRUE, FALSE, FALSE, FALSE, FALSE,
             FALSE, TRUE, FALSE, FALSE, FALSE, FALSE)
  )) +
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.1f", agreement * 100
    ), "%  ")),
    #color = agreement > .05
    #hjust = agreement > .05),
    hjust = "right",
    size = 5,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  scale_fill_manual(values = generate_palette("#37B7C3", 
                                              modification = "go_both_ways", 
                                              n_colours = 2))+
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(-0.05, 1.1),
    breaks = c(seq(0, 1, 0.2)),
    labels = scales::label_percent()
  ) +
  scale_y_discrete(
    labels = c(
      "ncr_completeness"       = "Пълнота",
      "ncr_contemporary"       = "Съвременност",
      "ncr_accuracy"           = "Надеждност",
      "ncr_validity"           = "Валидност",
      "ncr_representativness"  = "Представителност",
      "ncr_confidentiality"    = "Конфиденциалност",
      "ncr_patient_outcomes"   = "Клинично влияние",
      "ncr_influence"          = "Политическо влияние",
      "ncr_research"           = "Изследователско влияние",
      "ncr_cost_effectivness"  = "Разходна ефективност",
      "ncr_awareness"          = "Осведоменост",
      "ncr_collaboration"      = "Сътрудничество"
    )
  ) +
  theme(legend.position = "none") +
  labs(y = "", x = "%Одобрение")

# ggsave(
#  "ncr-agr-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 24,
#   height = 12
# )

pp |>
  dplyr::select(starts_with("ncr_")) |>
  ltm::cronbach.alpha(standardized = T, CI = T)

pp |>
  dplyr::select(starts_with("ncr_")) |>
  psych::alpha()

pp |>
  dplyr::select(starts_with("ncr_")) |>
  psych::KMO()

pp |>
  dplyr::select(starts_with("ncr_")) |>
  psych::cortest.bartlett()


  pp |> 
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63))) ) |>
  ungroup() |>
  dplyr::select(-c(starts_with("ncr_"))) |>
  group_by(country) |>
  summarise(
    n = n(),
    mean = mean(ncrsum, na.rm = TRUE),
    SE = sd(ncrsum, na.rm = TRUE) / sqrt(n()),
    lower = mean - 1.96 * SE,
    upper = mean + 1.96 * SE,
    "95%CI" = paste0(round(lower, 2), ", ", round(upper, 2))
  ) |>
  mutate(
    country = case_when(
      country == "Croatia" ~ "Хърватия",
      country == "Cyprus" ~ "Кипър",
      country == "Czech Republic" ~ "Чехия",
      country == "Denmark" ~ "Дания",
      country == "Finland" ~ "Финландия",
      country == "France" ~ "Франция",
      country == "Germany" ~ "Германия",
      country == "Greece" ~ "Гърция",
      country == "Ireland" ~ "Ирландия",
      country == "Italy" ~ "Италия",
      country == "Austria" ~ "Австрия",
      country == "Latvia" ~ "Латвия",
      country == "Lithuania" ~ "Литва",
      country == "Netherlands" ~ "Холандия",
      country == "Norway" ~ "Норвегия",
      country == "Poland" ~ "Полша",
      country == "Portugal" ~ "Португалия",
      country == "Slovakia" ~ "Словакия",
      country == "Slovenia" ~ "Словения",
      country == "Spain" ~ "Испания",
      country == "UK" ~ "Великобритания",
      country == "Belgium" ~ "Белгия",
      country == "Bulgaria" ~ "България",
      country == "Estonia" ~ "Естония",
      country == "Hungary" ~ "Унгария",
      country == "Malta" ~ "Малта",
      country == "Sweden" ~ "Швеция",
      country == "Switzerland" ~ "Швейцария"
    )
  ) |>
  mutate_round() |> 
  dplyr::select(country, n, mean, "95%CI") |>
  knitr::kable()
 
  
pp |> 
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63)))) |>
  ungroup() |>
  mutate(ncrsump = convert_prop(ncrsum)) |>
  dplyr::select(-c(starts_with("ncr_"))) |>  
  mutate(
    country = case_when(
      country == "Croatia" ~ "Хърватия",
      country == "Cyprus" ~ "Кипър",
      country == "Czech Republic" ~ "Чехия",
      country == "Denmark" ~ "Дания",
      country == "Finland" ~ "Финландия",
      country == "France" ~ "Франция",
      country == "Germany" ~ "Германия",
      country == "Greece" ~ "Гърция",
      country == "Ireland" ~ "Ирландия",
      country == "Italy" ~ "Италия",
      country == "Austria" ~ "Австрия",
      country == "Latvia" ~ "Латвия",
      country == "Lithuania" ~ "Литва",
      country == "Netherlands" ~ "Холандия",
      country == "Norway" ~ "Норвегия",
      country == "Poland" ~ "Полша",
      country == "Portugal" ~ "Португалия",
      country == "Slovakia" ~ "Словакия",
      country == "Slovenia" ~ "Словения",
      country == "Spain" ~ "Испания",
      country == "UK" ~ "Великобритания",
      country == "Belgium" ~ "Белгия",
      country == "Bulgaria" ~ "България",
      country == "Estonia" ~ "Естония",
      country == "Hungary" ~ "Унгария",
      country == "Malta" ~ "Малта",
      country == "Sweden" ~ "Швеция",
      country == "Switzerland" ~ "Швейцария"
    )
  ) |>
  aov(ncrsump ~ country, data = _) |>
  emmeans::emmeans(specs = c("country")) |>
  pairs(adjust = "bonferroni") |>
  tidy() |>
  mutate_round() |> 
  mutate(
    CI_low = estimate - 1.96 * std.error,
    CI_high = estimate + 1.96 * std.error,
    "95%CI" = paste0(round(CI_low, 2), ", ", round(CI_high, 2)),
    p = case_when(
      adj.p.value < 0.01 ~ "<.01",
      adj.p.value > 0.9 ~ "> .9",
      TRUE ~ as.character(adj.p.value)
    )
  ) |> 
  dplyr::select(2,4,7,11,12) |>
  knitr::kable()
  
  eu_countries |>
    left_join(
        pp |> 
        rowwise() |>
        mutate(ncrsum = sum(across(c(52:63)))) |>
        ungroup() |>
        mutate(ncrsump = convert_prop(ncrsum)) |>
        dplyr::select(-c(starts_with("ncr_"))) |>
        group_by(country) |>
        summarise(
          n = n(),
          mean = mean(ncrsump, na.rm = TRUE),
          SE = sd(ncrsump, na.rm = TRUE) / sqrt(n()),
          lower = mean - 1.96 * SE,
          upper = mean + 1.96 * SE,
          "95%CI" = paste0(round(lower, 2), ", ", round(upper, 2))
        )
    ) |>
    ggplot(aes(x = long, y = lat, group = group)) +
    geom_polygon(
      aes(fill = mean),
      alpha = 1.4,
      color = "black",
      lty = 1,
      linewidth = 0.2
    ) +
    theme_void() +
    theme(legend.position = "none") +
    scale_fill_gradient2(
      midpoint = 0.5,
      low = "#FFC96F",
      mid = "#68D2E8",
      high = "#003285"
    )
  
# ggsave(
#   "eu-ncr-map.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 11,
#   height = 11
# )
  
pp |>
  dplyr::select(starts_with("ncr_")) |> 
  correlation() |> 
  tibble() |> 
  mutate_round() |> 
  mutate(
    Parameter1 = case_when(
      Parameter1 == "ncr_completeness" ~ "Пълнота",
      Parameter1 == "ncr_contemporary" ~ "Съвременност",
      Parameter1 == "ncr_accuracy" ~ "Надеждност",
      Parameter1 == "ncr_validity" ~ "Валидност",
      Parameter1 == "ncr_representativness" ~ "Представителност",
      Parameter1 == "ncr_confidentiality" ~ "Конфиденциалност",
      Parameter1 == "ncr_patient_outcomes" ~ "Клинично влияние",
      Parameter1 == "ncr_influence" ~ "Политическо влияние",
      Parameter1 == "ncr_research" ~ "Изследователско влияние",
      Parameter1 == "ncr_cost_effectivness" ~ "Разходна ефективност",
      Parameter1 == "ncr_awareness" ~ "Осведоменост",
      Parameter1 == "ncr_collaboration" ~ "Сътрудничество"
    ),
    Parameter2 = case_when(
      Parameter2 == "ncr_completeness" ~ "Пълнота",
      Parameter2 == "ncr_contemporary" ~ "Съвременност",
      Parameter2 == "ncr_accuracy" ~ "Надеждност",
      Parameter2 == "ncr_validity" ~ "Валидност",
      Parameter2 == "ncr_representativness" ~ "Представителност",
      Parameter2 == "ncr_confidentiality" ~ "Конфиденциалност",
      Parameter2 == "ncr_patient_outcomes" ~ "Клинично влияние",
      Parameter2 == "ncr_influence" ~ "Политическо влияние",
      Parameter2 == "ncr_research" ~ "Изследователско влияние",
      Parameter2 == "ncr_cost_effectivness" ~ "Разходна ефективност",
      Parameter2 == "ncr_awareness" ~ "Осведоменост",
      Parameter2 == "ncr_collaboration" ~ "Сътрудничество"
    )
  ) |>
  mutate(
    '95%CI' = paste0(round(CI_low, 2), ", ", round(CI_high, 2))
  ) |> 
  dplyr::select(Parameter1, Parameter2, r, '95%CI', t, p) |>
  knitr::kable()



pp |>
  dplyr::select(starts_with("ncr_")) |> 
  pivot_longer(cols = 1:12,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    variable = case_when(
      variable == "ncr_completeness" ~ "Пълнота",
      variable == "ncr_contemporary" ~ "Съвременност",
      variable == "ncr_accuracy" ~ "Надеждност",
      variable == "ncr_validity" ~ "Валидност",
      variable == "ncr_representativness" ~ "Представителност",
      variable == "ncr_confidentiality" ~ "Конфиденциалност",
      variable == "ncr_patient_outcomes" ~ "Клинично влияние",
      variable == "ncr_influence" ~ "Политическо влияние",
      variable == "ncr_research" ~ "Изследователско влияние",
      variable == "ncr_cost_effectivness" ~ "Разходна ефективност",
      variable == "ncr_awareness" ~ "Осведоменост",
      variable == "ncr_collaboration" ~ "Сътрудничество"
    )
  ) |>
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(specs = c("variable")) |>
  pairs(adjust = "bonferroni") |>
  tidy() |>
  dplyr::select(2, 4, 5, 7, 8) |>
  mutate_round() |> 
  mutate(
    p = case_when(
      adj.p.value < 0.01 ~ "<.01",
      adj.p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(adj.p.value)
    )
  ) |> 
  dplyr::select(-adj.p.value) |>
  knitr::kable()


pp |>
  count(ncr_completeness, ncr_validity) |>
  full_join(expand.grid(ncr_validity = 1:5, ncr_completeness = 1:5)) |>
  mutate(n = ifelse(is.na(n), 0, n),
         sum = sum(n),
         prop = n / sum) |>
  ggplot(aes(x = ncr_completeness, y = ncr_validity)) +
  geom_tile(
    aes(fill = prop),
    color = "white",
    alpha = 0.9,
    linewidth = 1
  ) +
  geom_text(
    aes(label = ifelse(prop > 0,
                       paste0("  ", sprintf(
                         "%2.1f", prop * 100
                       ), "%  "),
                       ""
    )),
    vjust = 0.5,
    hjust = 0.5,
    size = 5,
    family = "Roboto Condensed",
  ) +
  geom_rangeframe(data = tibble(
    ncr_completeness = c(1, 2, 3, 4, 5),
    ncr_validity = c(1, 2, 3, 4, 5)
  ), ) +
  scale_fill_gradient2(
    midpoint = 0.17,
    low = "white",
    mid = "#31B1C2",
    high = "#021526"
  ) +
  theme(legend.position = "none") +
  labs(x = "Пълнота", y = "Валидност")

# ggsave(
#   "ncr-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 22,
#   height = 14
# )


pp |>
  dplyr::select(starts_with("ncr_")) |> 
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
    Parameter1 =
      case_when(
        Parameter1 == "ncr_completeness" ~ "Пълнота",
        Parameter1 == "ncr_contemporary" ~ "Съвременност",
        Parameter1 == "ncr_accuracy" ~ "Надеждност",
        Parameter1 == "ncr_validity" ~ "Валидност",
        Parameter1 == "ncr_representativness" ~ "Представителност",
        Parameter1 == "ncr_confidentiality" ~ "Конфиденциалност",
        Parameter1 == "ncr_patient_outcomes" ~ "Клинично влияние",
        Parameter1 == "ncr_influence" ~ "Политическо влияние",
        Parameter1 == "ncr_research" ~ "Изследователско влияние",
        Parameter1 == "ncr_cost_effectivness" ~ "Разходна ефективност",
        Parameter1 == "ncr_awareness" ~ "Осведоменост",
        Parameter1 == "ncr_collaboration" ~ "Сътрудничество"
      ),
    Parameter2 =
      case_when(
        Parameter2 == "ncr_completeness" ~ "Пълнота",
        Parameter2 == "ncr_contemporary" ~ "Съвременност",
        Parameter2 == "ncr_accuracy" ~ "Надеждност",
        Parameter2 == "ncr_validity" ~ "Валидност",
        Parameter2 == "ncr_representativness" ~ "Представителност",
        Parameter2 == "ncr_confidentiality" ~ "Конфиденциалност",
        Parameter2 == "ncr_patient_outcomes" ~ "Клинично влияние",
        Parameter2 == "ncr_influence" ~ "Политическо влияние",
        Parameter2 == "ncr_research" ~ "Изследователско влияние",
        Parameter2 == "ncr_cost_effectivness" ~ "Разходна ефективност",
        Parameter2 == "ncr_awareness" ~ "Осведоменост",
        Parameter2 == "ncr_collaboration" ~ "Сътрудничество"
      ),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 45, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "", subtitle = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))

# ggsave(
#   "ncr-full-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 28,
#   height = 16
# )


ncr_models <-
  pp |>
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63))),
         cvpsum = sum(
           c(
             cpv_knowledge,
             cpv_perception,
             cpv_attitude,
             cpv_communication,
             cpv_reach,
             cpv_impact
           ))) |> 
  ungroup() |>
  dplyr::select(-c("country" , 
            starts_with("ncr_"), 
            starts_with("cpv_"))) |>
  dplyr::select(-c(45:67, 69)) |>
  univariate_predictors(outcome_var = "ncrsum") |>
  mutate_round()

ncr_models |>
  filter(p_lm_value < 0.05) |> 
  count(predictor)

pp |>
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63))),
         cvpsum = sum(
           c(
             cpv_knowledge,
             cpv_perception,
             cpv_attitude,
             cpv_communication,
             cpv_reach,
             cpv_impact
           ))) |> 
  ungroup() |> 
  lm(ncrsum ~ ncpsum  , data = _) |> 
  tidy() |> 
  mutate_round()


pp |>
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63))),
         cvpsum = sum(
           c(
             cpv_knowledge,
             cpv_perception,
             cpv_attitude,
             cpv_communication,
             cpv_reach,
             cpv_impact
           ))) |> 
  ungroup() |>
  dplyr::select(-c("country" , 
            starts_with("ncr_"), 
            starts_with("cpv_"))) |>
  dplyr::select(-c(45:67, 69)) |> 
  ggplot(aes(x = hcepc, y = ncrsum)) +
  geom_density_2d(alpha = 0.6, color = "#088395", ) +
  geom_point(color = "gray15",
             alpha = 0.6,
             size = 1.2) +
  geom_rangeframe(data = tibble(hcepc = c(650,10400), ncrsum = c(12, 60))) +
  geom_rug(
    color = "gray20",
    alpha = 0.6,
    position = "jitter"
  ) +
  geom_smooth(
    method = "lm",
    lty = 2,
    fill = "#36BA98",
    alpha = 0.6,
    size = 0.8,
    color = "gray10"
  ) +
  scale_y_continuous(
    expand = c(0, 0),
    limits = c(10, 64),
    breaks = c(seq(12, 62, 16))
  ) +
  scale_x_log10(guide = "axis_logticks", 
                limit = c(600, 10500),
                labels=dollar_format(prefix="$",
                                     accuracy = 1), 
                breaks = c(650, 1300, 2600, 5200, 10400)) +
  labs(x = "Публични разходи за здравеопазване на глава от населението", y = "НРР")

# ggsave(
#    "hcepp-ncr-bg.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 22,
#    height = 14
#  )



ncr_models |> 
  dplyr::select(1,2,12,3,4,7,8) |> 
  mutate(
    `95%CI` = paste0(round(conf.low, 2), ", ", round(conf.high, 2))
  )


pp |>
  dplyr::select(46:51) |>
  correlation() |>
  tibble()


pp |>
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63))),
         cvpsum = sum(
           c(
             cpv_knowledge,
             cpv_perception,
             cpv_attitude,
             cpv_communication,
             cpv_reach,
             cpv_impact
           ))) |> 
  ungroup() |>
  dplyr::select(-c("country" , 
            starts_with("ncr_"), 
            starts_with("cpv_"))) |>
  dplyr::select(-c(45:67, 69)) |> 
  ggplot(aes(x = cvpsum, y = ncrsum)) +
  geom_density_2d(alpha = 0.6, color = "#088395", ) +
  geom_point(color = "gray15",
             alpha = 0.6,
             size = 1.2) +
  geom_rangeframe(data = tibble(cvpsum = c(6, 30), ncrsum = c(12, 60))) +
  geom_rug(
    color = "gray20",
    alpha = 0.6,
    position = "jitter"
  ) +
  geom_smooth(
    method = "lm",
    lty = 2,
    fill = "#36BA98",
    alpha = 0.6,
    size = 0.8,
    color = "gray10"
  ) +
  scale_y_continuous(
    expand = c(0, 0),
    limits = c(12, 64),
    breaks = c(seq(12, 62, 16))
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(5, 31),
    breaks = c(seq(6, 40, 8))
  ) +
  labs(x = "Първична профилактика", y = "НРР")

# ggsave(
#    "pp-ncr-bg.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 22,
#    height = 14
#  )



pp |>
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63))),
         cvpsum = sum(
           c(
             cpv_knowledge,
             cpv_perception,
             cpv_attitude,
             cpv_communication,
             cpv_reach,
             cpv_impact
           ))) |> 
  ungroup() |>
  dplyr::select(-c("country" , 
            starts_with("ncr_"), 
            starts_with("cpv_"))) |>
  dplyr::select(-c(45:67, 69)) |> 
  ggplot(aes(x = ncpsum, y = ncrsum)) +
  geom_density_2d(alpha = 0.6, color = "#088395", ) +
  geom_point(color = "gray15",
             alpha = 0.6,
             size = 1.2) +
  geom_rangeframe(data = tibble(ncpsum = c(8, 40), 
                                ncrsum = c(12, 60))) +
  geom_rug(
    color = "gray20",
    alpha = 0.6,
    position = "jitter"
  ) +
  geom_smooth(
    method = "lm",
    lty = 2,
    fill = "#36BA98",
    alpha = 0.6,
    size = 0.8,
    color = "gray10"
  ) +
  scale_y_continuous(
    expand = c(0, 0),
    limits = c(10, 64),
    breaks = c(seq(12, 62, 16))
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(7, 42),
    breaks = c(seq(8, 40, 4))
  ) +
  labs(x = "Национални ракови планове", y = "Ракови регистри")

# ggsave(
#    "ncp-ncr-bg.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 22,
#    height = 14
#  )


  pp |>
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63))),
         cvpsum = sum(
           c(
             cpv_knowledge,
             cpv_perception,
             cpv_attitude,
             cpv_communication,
             cpv_reach,
             cpv_impact
           ))) |> 
  ungroup() |>
  pivot_longer(cols = c(64:70),
               names_to = "scrfund_variable",
               values_to = "scrfund_value") |>
  mutate(scrfund_variable = case_when(
    scrfund_variable == "scrfund_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
    scrfund_variable ==  "scrfund_other_industry"   ~ "Индустрия",
    scrfund_variable ==  "scrfund_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
    scrfund_variable ==  "scrfund_private_household_out_of_pocket_expenditure" ~ "Лични разходи на домакинствата",
    scrfund_variable ==  "scrfund_private_voluntary_health_insurance_funding" ~ "ДОФ",
    scrfund_variable ==  "scrfund_public_goverment_funding" ~ "Държавно финансиране",
    scrfund_variable ==  "scrfund_public_health_insurance_funding" ~ "ЗОФ")) |> 
  aov(scrfund_value ~ scrfund_variable, data = _) |>
    emmeans::emmeans(specs = "scrfund_variable") |>
    tidy() |>
    ggplot(aes(x = estimate, y = fct_reorder(scrfund_variable, estimate))) +
    geom_point(aes(color = scrfund_variable), size = 3) +
    geom_rangeframe(data = tibble(
      scrfund_variable = c(
        "ДОФ",
        "Държавно финансиране",      
        "ЗОФ",
        "Индустрия",                 
        "Лични разходи на домакинствата",
        "Програми и фондове на ЕС",  
        "Финансиране от НПО" 
      ),
      estimate = c(1, 5, 1, 1, 1, 1, 1)
    )) +
    geom_text(
      aes(label = paste0("  ", sprintf(
        "%2.2f", estimate
      ))),
      hjust = +0.5,
      vjust = -0.5,
      size = 5,
      fontface = "bold",
      family = "Roboto Condensed",
    ) +
    geom_errorbar(
      aes(
        xmin = estimate - 1.96 * std.error,
        xmax = estimate + 1.96 * std.error,
        colour = scrfund_variable
      ),
      width = 0.2,
      alpha = 0.7,
      size = 0.5,
    ) +
    geom_vline(
      xintercept = 2.70,
      lty = 2,
      size = 0.5,
      color = "gray10"
    ) +
    scale_x_continuous(
      expand = c(0, 0),
      limits = c(1, 5.5),
      breaks = c(seq(1, 5, 1))
    ) +
    theme(legend.position = "none") +
    scale_color_manual(values = c(
      "#03346E",
      "#03346E",
      "#03346E",
      "#973131",
      "#973131",
      "#059212",
      "#059212"
    )) +
    labs(x = "", y = "", subtitle = "")
  
# ggsave(
#   "mean-scr-finance-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 24,
#   height = 12
# )
  
  
  pp |>
    rowwise() |>
    mutate(ncrsum = sum(across(c(52:63))),
           cvpsum = sum(
             c(
               cpv_knowledge,
               cpv_perception,
               cpv_attitude,
               cpv_communication,
               cpv_reach,
               cpv_impact
             ))) |> 
    ungroup() |> 
    dplyr::select(64:70) |>
    pivot_longer(cols = 1:7,
                 names_to = "variable",
                 values_to = "value") |>
    mutate(
      fct_var = case_when(
        value == 1 ~ "no",
        value == 2 ~ "no",
        value == 3 ~ "both",
        value == 4 ~ "yes",
        value == 5 ~ "yes"
      )
    ) |>
    count(variable, fct_var) |>
    group_by(variable) |>
    pivot_wider(names_from = fct_var, values_from = n) |>
    mutate(
      agreement = (yes + 0.5 * both) / 92,
      disagreement = (no + 0.5 * both) / 92,
      adr = agreement / disagreement,
      adr1 = ifelse(adr > 1, TRUE, FALSE)
    ) |>
    dplyr::select(variable, agreement, disagreement, adr, adr1) |>
    ggplot(aes(
      x = agreement,
      y = fct_reorder(variable, agreement),
      fill = adr1
    )) +
    geom_col(color = "gray10", alpha = 0.7) +
    geom_vline(
      xintercept = 0.5,
      lty = 2,
      size = 0.5,
      color = "#013440"
    ) +
    geom_rangeframe(data = tibble(
      variable = c(
        "scrfund_other_eu_financing_project_lines",
        "scrfund_other_industry",
        "scrfund_other_non_profit_institutions_serving_households",
        "scrfund_private_household_out_of_pocket_expenditure",
        "scrfund_private_voluntary_health_insurance_funding",
        "scrfund_public_goverment_funding",
        "scrfund_public_health_insurance_funding"
      ),
      agreement = c(0, 1, 0, 0, 0, 0, 0),
      adr1 = c(FALSE, FALSE, TRUE, FALSE, FALSE, FALSE, FALSE)
    )) +
    geom_text(
      aes(label = paste0("  ", sprintf(
        "%2.1f", agreement * 100
      ), "%  ")),
      #color = agreement > .05
      #hjust = agreement > .05),
      hjust = "right",
      size = 5,
      fontface = "bold",
      family = "Roboto Condensed",
    ) +
    scale_fill_manual(values = generate_palette("#37B7C3", 
                                                modification = "go_both_ways", 
                                                n_colours = 2)) +
    scale_x_continuous(
      expand = c(0, 0),
      limits = c(-0.05, 1.1),
      breaks = c(seq(0, 1, 0.2)),
      labels = scales::label_percent()
    ) +
    scale_y_discrete(
      labels = c(
        "scrfund_other_eu_financing_project_lines" = "Програми и фондове на ЕС",
        "scrfund_other_industry" = "Индустрия",
        "scrfund_other_non_profit_institutions_serving_households" = "Финансиране от НПО",
        "scrfund_private_household_out_of_pocket_expenditure" = "Лични разходи",
        "scrfund_private_voluntary_health_insurance_funding" = "ДОФ",
        "scrfund_public_goverment_funding" = "Държавно финансиране",
        "scrfund_public_health_insurance_funding" = "ЗОФ"
    )) +
    theme(legend.position = "none") +
    labs(y = "", x = "%Одобрение")
  
#  ggsave(
#    "scr-finance-bg.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 24,
#    height = 12
#  )
  

ncp_funding <- 
  gp |>
    dplyr::select(48:54) |>
    pivot_longer(cols = 1:7,
                 names_to = "variable",
                 values_to = "plan_value") |> 
  mutate(
    variable = str_replace(variable, "ncp_funding_", "")) |>
  mutate(rowid = row_number())


sc_funding <- 
  pp |> 
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63))),
         cvpsum = sum(
           c(
             cpv_knowledge,
             cpv_perception,
             cpv_attitude,
             cpv_communication,
             cpv_reach,
             cpv_impact
           ))) |> 
  ungroup() |> 
  dplyr::select(64:70) |>
  pivot_longer(cols = 1:7,
               names_to = "screen_variable",
               values_to = "screen_value") |> 
  mutate(
    screen_variable = str_replace(screen_variable, "scrfund_", "")) |> 
  mutate(rowid = row_number())

ncp_funding |> 
  left_join(sc_funding, by = "rowid") |>
  dplyr::select(-c(rowid, screen_variable)) |> 
  pivot_longer(cols = 2:3,
               names_to = "evaluation",
               values_to = "num") |>
  mutate(
     fct_var = case_when(
       num == 1 ~ "no",
       num == 2 ~ "no",
       num == 3 ~ "both",
       num == 4 ~ "yes",
       num == 5 ~ "yes"
    )
  ) |> 
  mutate(
    category = sub("_.*", "",variable)) |> 
  count(evaluation,variable, fct_var) |>
  group_by(evaluation,variable) |>
  pivot_wider(names_from = fct_var, values_from = n) |>
  mutate(
    agreement = (yes + 0.5 * both), 
    sum = 92
  ) |> 
  dplyr::select(1,2,6,7) |> 
  mutate(agreement    = as.integer(agreement),
         sum = as.integer(sum)) |>
  group_by(variable) |>
  nest() |> 
  mutate(comparison = map(data, ~
                            .x |> 
                                pcit() |> 
                                compare_proportions()
  )) |> 
  unnest(comparison) 

pp |>
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63))),
         cvpsum = sum(
           c(
             cpv_knowledge,
             cpv_perception,
             cpv_attitude,
             cpv_communication,
             cpv_reach,
             cpv_impact
           ))) |> 
  ungroup() |> 
  dplyr::select(64:70) |>
  correlation::correlation() |>
  tibble() |>
  arrange(-r) |> 
  mutate_round() |> 
  mutate(Parameter1  = case_when(
    Parameter1  == "scrfund_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
    Parameter1  ==  "scrfund_other_industry"   ~ "Индустрия",
    Parameter1  ==  "scrfund_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
    Parameter1  ==  "scrfund_private_household_out_of_pocket_expenditure" ~ "Лични разходи на домакинствата",
    Parameter1  ==  "scrfund_private_voluntary_health_insurance_funding" ~ "ДОФ",
    Parameter1  ==  "scrfund_public_goverment_funding" ~ "Държавно финансиране",
    Parameter1  ==  "scrfund_public_health_insurance_funding" ~ "ЗОФ"),
    Parameter2  = case_when(
      Parameter2  == "scrfund_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
      Parameter2  ==  "scrfund_other_industry"   ~ "Индустрия",
      Parameter2  ==  "scrfund_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
      Parameter2  ==  "scrfund_private_household_out_of_pocket_expenditure" ~ "Лични разходи на домакинствата",
      Parameter2  ==  "scrfund_private_voluntary_health_insurance_funding" ~ "ДОФ",
      Parameter2  ==  "scrfund_public_goverment_funding" ~ "Държавно финансиране",
      Parameter2  ==  "scrfund_public_health_insurance_funding" ~ "ЗОФ")) |> 
  mutate(
    '95%CI' = paste0(round(CI_low, 2), ", ", round(CI_high, 2)), 
     p = case_when(
       p < 0.01 ~ "<.01",
       p > 0.90 ~ "> .90",
      TRUE ~ as.character(p))) |> 
  dplyr::select(Parameter1, Parameter2, r, '95%CI', p) |>
  knitr::kable()


pp |> 
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63))),
         cvpsum = sum(
           c(
             cpv_knowledge,
             cpv_perception,
             cpv_attitude,
             cpv_communication,
             cpv_reach,
             cpv_impact
           ))) |> 
  ungroup() |> 
  dplyr::select(64:70) |>
  pivot_longer(cols = 1:7,
               names_to = "screen_variable",
               values_to = "screen_value") |> 
  mutate(screen_variable = case_when(
    screen_variable ==  "scrfund_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
    screen_variable ==  "scrfund_other_industry"   ~ "Индустрия",
    screen_variable ==  "scrfund_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
    screen_variable ==  "scrfund_private_household_out_of_pocket_expenditure" ~ "Лични разходи на домакинствата",
    screen_variable ==  "scrfund_private_voluntary_health_insurance_funding" ~ "ДОФ",
    screen_variable ==  "scrfund_public_goverment_funding" ~ "Държавно финансиране",
    screen_variable ==  "scrfund_public_health_insurance_funding" ~ "ЗОФ")) |> 
  aov(screen_value ~ screen_variable, data = _) |>
  emmeans::emmeans(specs = "screen_variable") |>
  pairs(adjust = "bonferroni") |>
  tidy() |>
  dplyr::select(2, 4, 5, 7, 8) |>
  arrange(-estimate) |>
  mutate_round() |>
  mutate(
    conf.low = estimate - 1.96 * std.error,
    conf.high = estimate + 1.96 * std.error,
    "95CI" = paste0(round(conf.low, 2), ", ", round(conf.high, 2))
  ) |> 
  mutate(
    p = case_when(
      adj.p.value < 0.01 ~ "<.01",
      adj.p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(adj.p.value)
    )
  ) |>
  dplyr::select(-c(3,5,6,7)) |>
  knitr::kable()


pp |> 
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63))),
         cvpsum = sum(
           c(
             cpv_knowledge,
             cpv_perception,
             cpv_attitude,
             cpv_communication,
             cpv_reach,
             cpv_impact
           ))) |> 
  ungroup() |> 
  dplyr::select(country, 64:70) |>
  pivot_longer(cols = 2:8,
               names_to = "screen_variable",
               values_to = "screen_value") |> 
  mutate(screen_variable = case_when(
    screen_variable == "scrfund_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
    screen_variable ==  "scrfund_other_industry"   ~ "Индустрия",
    screen_variable ==  "scrfund_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
    screen_variable ==  "scrfund_private_household_out_of_pocket_expenditure" ~ "Лични разходи на домакинствата",
    screen_variable ==  "scrfund_private_voluntary_health_insurance_funding" ~ "ДОФ",
    screen_variable ==  "scrfund_public_goverment_funding" ~ "Държавно финансиране",
    screen_variable ==  "scrfund_public_health_insurance_funding" ~ "ЗОФ")) |> 
  aov(screen_value ~ screen_variable + country, data = _) |>
  emmeans::emmeans(specs = c("screen_variable", "country"), 
                   adjust = "Bonferroni") |>
  tidy() |>
  mutate(
    country = case_when(
      country == "Croatia" ~ "Хърватия",
      country == "Cyprus" ~ "Кипър",
      country == "Czech Republic" ~ "Чехия",
      country == "Denmark" ~ "Дания",
      country == "Finland" ~ "Финландия",
      country == "France" ~ "Франция",
      country == "Germany" ~ "Германия",
      country == "Greece" ~ "Гърция",
      country == "Ireland" ~ "Ирландия",
      country == "Italy" ~ "Италия",
      country == "Austria" ~ "Австрия",
      country == "Latvia" ~ "Латвия",
      country == "Lithuania" ~ "Литва",
      country == "Netherlands" ~ "Холандия",
      country == "Norway" ~ "Норвегия",
      country == "Poland" ~ "Полша",
      country == "Portugal" ~ "Португалия",
      country == "Slovakia" ~ "Словакия",
      country == "Slovenia" ~ "Словения",
      country == "Spain" ~ "Испания",
      country == "UK" ~ "Великобритания",
      country == "Belgium" ~ "Белгия",
      country == "Bulgaria" ~ "България",
      country == "Estonia" ~ "Естония",
      country == "Hungary" ~ "Унгария",
      country == "Malta" ~ "Малта",
      country == "Sweden" ~ "Швеция",
      country == "Switzerland" ~ "Швейцария"
    ),
  ) |>
  dplyr::select(2,1,3,4,6,7) |>
  mutate_round() |>
  mutate(
    conf.low = estimate - 1.96 * std.error,
    conf.high = estimate + 1.96 * std.error,
    "95CI" = paste0(round(conf.low, 2), ", ", round(conf.high, 2))
  ) |> 
  mutate(
    p = case_when(
      adj.p.value < 0.01 ~ "<.01",
      adj.p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(adj.p.value)
    )
  ) |>
  dplyr::select(-c(4,6,7,8)) |>
  knitr::kable()
  

scr_fnd_models <- 
  pp |> 
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63))),
         cvpsum = sum(
           c(
             cpv_knowledge,
             cpv_perception,
             cpv_attitude,
             cpv_communication,
             cpv_reach,
             cpv_impact
           ))) |> 
  ungroup() |> 
  pivot_longer(cols = 64:70,
               names_to = "screen_fnd_variable",
               values_to = "screen_fnd_value") |> 
  dplyr::select(-c(2,38:44, 46:79,81)) |>
  group_by(screen_fnd_variable) |>
  nest() |>
  mutate(
    models = map(data, ~
                        .x |> 
                          to_dummmy() |> 
                          univariate_predictors(outcome_var = "screen_fnd_value")))



scr_fnd_models |> 
  unnest(models) |>
  mutate_if(is.numeric, round, 2) |> 
  dplyr::select(-data) |>
  group_by(screen_fnd_variable) |> 
  filter(p_lm_value < 0.05) |>
  dplyr::select(1,2,13,3,4,8,9,7) |> 
  mutate(
    screen_fnd_variable = case_when(
      screen_fnd_variable == "scrfund_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",
      screen_fnd_variable ==  "scrfund_other_industry"   ~ "Индустрия",
      screen_fnd_variable ==  "scrfund_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
      screen_fnd_variable ==  "scrfund_private_household_out_of_pocket_expenditure" ~ "Лични разходи",
      screen_fnd_variable ==  "scrfund_private_voluntary_health_insurance_funding" ~ "ДОФ",
      screen_fnd_variable ==  "scrfund_public_goverment_funding" ~ "Държавно финансиране",
      screen_fnd_variable ==  "scrfund_public_health_insurance_funding" ~ "ЗОФ")) |> 
  mutate(
    "95%CI" = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
    p.value = case_when(
      p.value < 0.01 ~ "<.001",
      p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(p.value)), 
    p_lm_value = case_when(
      p_lm_value < 0.01 ~ "<.001",
      p_lm_value > 0.90 ~ "> .90",
        TRUE ~ as.character(p_lm_value)
    )
  ) |> 
  dplyr::select(1,2,3,4,5,8,9) |>
  dplyr::select(-p.value) |> 
  flextable::flextable() 


scr_fnd_models |> 
     unnest(models) |>
     mutate_if(is.numeric, round, 2) |> 
     dplyr::select(-data) |>
     group_by(screen_fnd_variable) |>
     filter(p_lm_value < 0.05) |> 
  count(screen_fnd_variable)


scr_fnd_models |> 
  unnest(models) |>
  mutate_if(is.numeric, round, 2) |> 
  dplyr::select(-data) |> 
  filter(p_lm_value < 0.05 &
           screen_fnd_variable == "scrfund_private_voluntary_health_insurance_funding") |>
  count(predictor) 


pp |> 
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63))),
         cvpsum = sum(
           c(
             cpv_knowledge,
             cpv_perception,
             cpv_attitude,
             cpv_communication,
             cpv_reach,
             cpv_impact
           ))) |> 
  ungroup() |> 
  pivot_longer(cols = 64:70,
               names_to = "screen_fnd_variable",
               values_to = "screen_fnd_value") |> 
  dplyr::select(-c(2,38:44, 46:79,81)) |> 
  filter(screen_fnd_variable == "scrfund_private_voluntary_health_insurance_funding") |>
  to_dummmy() |>
  lm(screen_fnd_value ~ area_of_rare_cancers_paediatric_cancers, data = _) 


pp |> 
  dplyr::select(starts_with("imp_")) |>
  pivot_longer(cols = 1:6,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    fct_var = case_when(
      value == 1 ~ "no",
      value == 2 ~ "no",
      value == 3 ~ "both",
      value == 4 ~ "yes",
      value == 5 ~ "yes"
    )
  ) |>
  count(variable, fct_var) |>
  group_by(variable) |>
  pivot_wider(names_from = fct_var, values_from = n) |>
  mutate(
    agreement = (yes + 0.5 * both) / 92,
    disagreement = (no + 0.5 * both) / 92,
    adr = agreement / disagreement,
    adr1 = ifelse(adr > 1, TRUE, FALSE)
  ) |>
  dplyr::select(variable, agreement, disagreement, adr, adr1) |>
  ggplot(aes(
    x = agreement,
    y = fct_reorder(variable, agreement),
    fill = adr1
  )) +
  geom_col(color = "gray10", alpha = 0.7) +
  geom_vline(
    xintercept = 0.5,
    lty = 2,
    size = 0.5,
    color = "#013440"
  ) +
  geom_rangeframe(data = tibble(
    variable = c(
      "imp_breast_cancer_screening",                   
      "imp_helicobacter_pylori_for_gastric_ca",        
      "imp_low_dose_computed_tomography_lung_cancer",  
      "imp_psa",                                       
      "imp_quantitative_faecal_immunochemical_testing",
      "imp_testing_for_human_papilloma_virus_hpv"    
    ),
    agreement = c(0, 1, 0, 
                  0, 0, 0),
    adr1 = c(FALSE, FALSE, FALSE, 
             TRUE, FALSE, FALSE)
  )) +
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.1f", agreement * 100
    ), "%  ")),
    #color = agreement > .05
    #hjust = agreement > .05),
    hjust = "right",
    size = 5,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  scale_fill_manual(values = generate_palette("#37B7C3", 
                                              modification = "go_both_ways", 
                                              n_colours = 2))+
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(-0.05, 1.1),
    breaks = c(seq(0, 1, 0.2)),
    labels = scales::label_percent()
  ) +
  scale_y_discrete(
    labels = c(
      "imp_breast_cancer_screening" = "Мамография за Ca на гърдата",    
      "imp_helicobacter_pylori_for_gastric_ca" = "H. pylori тест за Ca на стомаха",      
      "imp_low_dose_computed_tomography_lung_cancer" = "НДКТ за Ca на белите дробове", 
      "imp_psa" = "PSA ~> MRI за Ca на простата",                                       
      "imp_quantitative_faecal_immunochemical_testing" = "qFIT ~> Колоноскопия за Ca на дебело черво",
      "imp_testing_for_human_papilloma_virus_hpv" = "HPV тест за РМШ" 
    )
  ) +
  theme(legend.position = "none") +
  labs(y = "", x = "%Одобрение")

# ggsave(
#   "scr-imp-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 24,
#   height = 12
# )

pp |> 
  dplyr::select(hcepc_hight, starts_with("imp_")) |>
  pivot_longer(
    cols = 2:7,
    names_to = "variable",
    values_to = "value"
  ) |>
  mutate(
    fct_var = case_when(
      value == 1 ~ "no",
      value == 2 ~ "no",
      value == 3 ~ "both",
      value == 4 ~ "yes",
      value == 5 ~ "yes"
    )
  ) |> 
  group_by(variable) |>
  nest() |> 
  mutate(agrmnt = map(data, ~
                            .x |> 
                        count(hcepc_hight, fct_var) |>
                        pivot_wider(names_from = fct_var, values_from = n) |>
                        replace_na(list(no = 0, both = 0, yes = 0)) |>
                        group_by(hcepc_hight) |>
                        mutate(sum = yes + no + both) |>
                        ungroup() |>
                        dplyr::select(hcepc_hight, yes, sum) |>
                        pcit() |> 
                        compare_proportions()
  )
  ) |> 
  unnest(agrmnt)

  
pp |> 
  dplyr::select(hcepc, starts_with("imp_")) |>
  correlation(select = "hcepc", select2 = c(
"imp_breast_cancer_screening",                   
"imp_testing_for_human_papilloma_virus_hpv",     
"imp_quantitative_faecal_immunochemical_testing",
"imp_low_dose_computed_tomography_lung_cancer",  
"imp_psa",                                       
"imp_helicobacter_pylori_for_gastric_ca"), 
method = "kendall")


# pp |> 
#   mutate(
#     imp_breast_cancer_screening = as.factor(imp_breast_cancer_screening)
#   ) |>
#   clm(imp_breast_cancer_screening ~ ncpsum, data = _) |> 
#   tidy(exp = TRUE, 
#        conf.int = TRUE)




scr_imp_models <- 
  pp |> 
  rowwise() |>
  mutate(ncrsum = sum(across(c(52:63))),
         cvpsum = sum(
           c(
             cpv_knowledge,
             cpv_perception,
             cpv_attitude,
             cpv_communication,
             cpv_reach,
             cpv_impact
           ))) |> 
  ungroup() |> 
  pivot_longer(cols = 71:76,
               names_to = "screen_imp_variable",
               values_to = "screen_imp_value") |> 
  dplyr::select(-c(2,
                   38:44,
                   46:63,
                   71:81,
                   82)) |> 
  group_by(screen_imp_variable) |>
  nest() |>
  mutate(
    models = map(data, ~
                   .x |> 
                   to_dummmy() |>
                   collect_model_results(outcome_var = "screen_imp_value")))



scr_imp_models |> 
  unnest(models) |> 
  mutate_if(is.numeric, round, 2) |>
  dplyr::select(-data) |>
  group_by(screen_imp_variable) |>
  filter(model_p_value < 0.05) |>
  dplyr::select(1,2,3,4,7,8,9,10) |>
  mutate(
    screen_imp_variable = case_when(
      screen_imp_variable == "imp_breast_cancer_screening" ~ "Мамография за Ca на гърдата",
      screen_imp_variable ==  "imp_helicobacter_pylori_for_gastric_ca"   ~ "H. pylori тест за Ca на стомаха",
      screen_imp_variable ==  "imp_low_dose_computed_tomography_lung_cancer" ~ "НДКТ за Ca на белите дробове",
      screen_imp_variable ==  "imp_psa" ~ "PSA ~> MRI за Ca на простата",
      screen_imp_variable ==  "imp_quantitative_faecal_immunochemical_testing" ~ "qFIT ~> Колоноскопия за Ca на дебело черво",
      screen_imp_variable ==  "imp_testing_for_human_papilloma_virus_hpv" ~ "HPV тест за РМШ"
    )
  ) |>
  dplyr::select(-term) |> 
  mutate(
    "95%CI" = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
    p.value = case_when(
      p.value < 0.01 ~ "<.001",
      p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(p.value)
    )) |> 
  dplyr::select(1,2,7,3,4,8)



pp |>
  dplyr::select(starts_with("eucbp_")) |>
  pivot_longer(cols = 1:10,
               names_to = "variable",
               values_to = "value") |> 
  mutate(variable =
           case_when(
             variable ==        "eucbp_addressing_unhealthy_diets_obesity_and_physical_inactivity" ~ "↓ Карциногенните в храните",
             variable == 
               "eucbp_adoption_of_a_new_occupational_safety_and_health_strategic_framework" ~
               "↓ Експозицията към химическо замърсяване на работа",
             variable == "eucbp_alignment_of_the_e_us_air_quality_standards_more_closely_with_the_who_guidelines" ~ 
               "≃ Стандартите за КАВ в ЕС със СЗО",
             variable == "eucbp_creation_of_a_knowledge_centre" ~ "Център за координация на ракови инициативи",  
             variable == "eucbp_creation_of_a_tobacco_free_generation" ~ "↑ Регулацията на тютюневите изделия в ЕС", 
             variable == "eucbp_developing_a_new_eu_cancer_screening_scheme" ~ 
               "↑ Достъп до скрининг за КРК, РМЖ, РШМ",
             variable == "eucbp_elimination_of_cancers_caused_by_human_papillomaviruses_vaccination" ~ 
               "↑ Ваксинацията срещу HPV",
             variable == "eucbp_enabling_cancer_patients_to_securely_access_and_share_electronic_health_records" ~ 
               "Споделяне на ЕЗЗ през ЕЗДП", 
             variable == "eucbp_improvement_of_health_literacy_on_cancer_risk_by_updating_the_european_code" ~ 
               "⟲ Европейския раков кодекс",
             variable == "eucbp_reducing_the_harmful_alcohol_consumption"  ~
               "↓ Злоупотребата с алкохол")) |> 
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(specs = "variable") |>
  tidy() |>
  ggplot(aes(x = estimate, y = fct_reorder(variable, estimate))) +
  geom_point(size = 3) +
  geom_rangeframe(data = tibble(
    variable = c(
      "↓ Карциногенните в храните",                        
      "↓ Експозицията към химическо замърсяване на работа",
      "≃ Стандартите за КАВ в ЕС със СЗО",    
      "Център за координация на ракови инициативи",        
      "↑ Регулацията на тютюневите изделия в ЕС",          
      "↑ Достъп до скрининг за КРК, РМЖ, РШМ",             
      "↑ Ваксинацията срещу HPV",                          
      "Споделяне на ЕЗЗ през ЕЗДП",                        
      "⟲ Европейския раков кодекс",                       
      "↓ Злоупотребата с алкохол"), 
    estimate = c(1, 5, 1, 
                 1, 1, 1,
                 1, 1, 1, 
                 1))
  )+
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.2f", estimate
    ))),
    hjust = +0.5,
    vjust = -0.52,
    size = 5,
    family = "Sofia Sans Condensed",
  ) +
  geom_errorbar(
    aes(
      xmin = estimate - 1.96 * std.error,
      xmax = estimate + 1.96 * std.error
    ),
    width = 0.2,
    alpha = 0.7,
    size = 0.5,
  ) +
  geom_vline(
    xintercept = 3.95,
    lty = 2,
    size = 0.5,
    color = "gray10"
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(1, 5.5),
    breaks = c(seq(1, 5, 1))
  ) +
  scale_y_discrete(label = scales::label_wrap(40))+
  theme(legend.position = "none") +
  labs(x = "", y = "", subtitle = "")

#  ggsave(
#    "mean-eucbp-bg.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 25,
#    height = 14
#  )



 ppbg <- 
   pp |> 
  rename("↓ Карциногенните в храните" =       "eucbp_addressing_unhealthy_diets_obesity_and_physical_inactivity", 
         "↓ Експозицията към химическо замърсяване на работа" = "eucbp_adoption_of_a_new_occupational_safety_and_health_strategic_framework",
         "≃ Стандартите за КАВ в ЕС със СЗО" = "eucbp_alignment_of_the_e_us_air_quality_standards_more_closely_with_the_who_guidelines",
         "Център за координация на ракови инициативи" = "eucbp_creation_of_a_knowledge_centre",
         "↑ Регулацията на тютюневите изделия в ЕС" = "eucbp_creation_of_a_tobacco_free_generation",
         "↑ Достъп до скрининг за КРК, РМЖ, РШМ" = "eucbp_developing_a_new_eu_cancer_screening_scheme",
         "↑ Ваксинацията срещу HPV" =
         "eucbp_elimination_of_cancers_caused_by_human_papillomaviruses_vaccination" ,
         "Споделяне на ЕЗЗ през ЕЗДП" =
         "eucbp_enabling_cancer_patients_to_securely_access_and_share_electronic_health_records",
         "⟲ Европейския раков кодекс" = "eucbp_improvement_of_health_literacy_on_cancer_risk_by_updating_the_european_code",
         "↓ Злоупотребата с алкохол" = "eucbp_reducing_the_harmful_alcohol_consumption")


  ppbg |> 
  dplyr::select(77:86) |>
  ltm::cronbach.alpha(standardized = T, CI = T)

  ppbg |>
  dplyr::select(77:86) |>
  psych::alpha()

  ppbg |> 
  dplyr::select(77:86) |>
  psych::KMO()

  ppbg |> 
  dplyr::select(77:86) |>
  psych::cortest.bartlett()

  pp |>
  rowwise() |>
  mutate(eurecpp = sum(across(c(77:86)))) |>
  ungroup() |>
  dplyr::select(-c(starts_with("eucbp_"))) |>
  dlookr::normality(eurecpp)


  pp |>
  rowwise() |>
  mutate(eurecpp = sum(across(c(77:86)))) |>
  ungroup() |>
  dplyr::select(-c(starts_with("eucbp_"))) |>
  get_summary_stats(eurecpp)



ppbg |>
  dplyr::select(77:86) |>
  correlation() |>
  tibble() |>
  mutate_if(is.numeric, round, 2) |>
  mutate(CI = paste0("[", CI_low, ", ", CI_high, "]")) |>
  dplyr::select(Parameter1, Parameter2, r, CI, p) |>
  knitr::kable()



  pp |> 
  rowwise() |>
  mutate(eurecpp = sum(across(c(77:86)))) |>
  ungroup() |>
  dplyr::select(-c(starts_with("eucbp_"))) |>
  group_by(country) |>
  summarise(
    n = n(),
    mean = mean(eurecpp, na.rm = TRUE),
    SE = sd(eurecpp, na.rm = TRUE) / sqrt(n()),
    lower = mean - 1.96 * SE,
    upper = mean + 1.96 * SE,
    "95%CI" = paste0(round(lower, 2), ", ", round(upper, 2))
  ) |>
  mutate(
    country = case_when(
      country == "Croatia" ~ "Хърватия",
      country == "Cyprus" ~ "Кипър",
      country == "Czech Republic" ~ "Чехия",
      country == "Denmark" ~ "Дания",
      country == "Finland" ~ "Финландия",
      country == "France" ~ "Франция",
      country == "Germany" ~ "Германия",
      country == "Greece" ~ "Гърция",
      country == "Ireland" ~ "Ирландия",
      country == "Italy" ~ "Италия",
      country == "Austria" ~ "Австрия",
      country == "Latvia" ~ "Латвия",
      country == "Lithuania" ~ "Литва",
      country == "Netherlands" ~ "Холандия",
      country == "Norway" ~ "Норвегия",
      country == "Poland" ~ "Полша",
      country == "Portugal" ~ "Португалия",
      country == "Slovakia" ~ "Словакия",
      country == "Slovenia" ~ "Словения",
      country == "Spain" ~ "Испания",
      country == "UK" ~ "Великобритания",
      country == "Belgium" ~ "Белгия",
      country == "Bulgaria" ~ "България",
      country == "Estonia" ~ "Естония",
      country == "Hungary" ~ "Унгария",
      country == "Malta" ~ "Малта",
      country == "Sweden" ~ "Швеция",
      country == "Switzerland" ~ "Швейцария"
    )
  ) |>
  mutate_round() |> 
  dplyr::select(country, n, mean, "95%CI") |>
  knitr::kable()



eu_countries |>
  left_join(pp |> 
              rowwise() |>
              mutate(eurecpp = sum(across(c(77:86)))) |>
              ungroup() |>
              dplyr::select(-c(starts_with("eucbp_"))) |>
              group_by(country) |>
              summarise(
                n = n(),
                mean = mean(eurecpp, na.rm = TRUE),
                SE = sd(eurecpp, na.rm = TRUE) / sqrt(n()),
                lower = mean - 1.96 * SE,
                upper = mean + 1.96 * SE,
                "95%CI" = paste0(round(lower, 2), ", ", round(upper, 2))
              ) |>
              mutate(mean = convert_prop (mean)) ) |>
  ggplot(aes(x = long, y = lat, group = group)) +
  geom_polygon(
    aes(fill = mean),
    alpha = 1.4,
    color = "black",
    lty = 1,
    linewidth = 0.2
  ) +
  theme_void() +
  theme(legend.position = "none") +
  scale_fill_gradient2(
    midpoint = 0.5,
    low = "#FFC96F",
    mid = "#68D2E8",
    high = "#003285"
  )

# ggsave(
#   "eu-pp-rec-map.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 11,
#   height = 11
# )



pp |>
  dplyr::select(starts_with("eucbp_")) |>
  pivot_longer(cols = 1:10,
               names_to = "variable",
               values_to = "value") |> 
  mutate(variable =
           case_when(
             variable ==        "eucbp_addressing_unhealthy_diets_obesity_and_physical_inactivity" ~ "↓ Карциногенните в храните",
             variable == 
               "eucbp_adoption_of_a_new_occupational_safety_and_health_strategic_framework" ~
               "↓ Експозицията към химическо замърсяване на работа",
             variable == "eucbp_alignment_of_the_e_us_air_quality_standards_more_closely_with_the_who_guidelines" ~ 
               "≃ Стандартите за КАВ в ЕС със СЗО",
             variable == "eucbp_creation_of_a_knowledge_centre" ~ "Център за координация на ракови инициативи",  
             variable == "eucbp_creation_of_a_tobacco_free_generation" ~ "↑ Регулацията на тютюневите изделия в ЕС", 
             variable == "eucbp_developing_a_new_eu_cancer_screening_scheme" ~ 
               "↑ Достъп до скрининг за КРК, РМЖ, РШМ",
             variable == "eucbp_elimination_of_cancers_caused_by_human_papillomaviruses_vaccination" ~ 
               "↑ Ваксинацията срещу HPV",
             variable == "eucbp_enabling_cancer_patients_to_securely_access_and_share_electronic_health_records" ~ 
               "Споделяне на ЕЗЗ през ЕЗДП", 
             variable == "eucbp_improvement_of_health_literacy_on_cancer_risk_by_updating_the_european_code" ~ 
               "⟲ Европейския раков кодекс",
             variable == "eucbp_reducing_the_harmful_alcohol_consumption"  ~
               "↓ Злоупотребата с алкохол")) |> 
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(specs = "variable") |>
  pairs(adjust = "bonferroni") |>
  tidy() |>
  dplyr::select(2,4,8) |>
  mutate_round() |> 
  mutate(
    adj.p.value = case_when(
      adj.p.value < 0.01 ~ "<.01",
      adj.p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(adj.p.value)
    )
  ) |> 
  knitr::kable()



pp |> 
  select(country, starts_with("eucbp_")) |>
  pivot_longer(cols = 2:11,
               names_to = "variable",
               values_to = "value") |>
  group_by(country, variable) |>
  summarise(
    n = n(),
    mean = mean(value, na.rm = TRUE),
    SE = sd(value, na.rm = TRUE) / sqrt(n()),
    lower = mean - 1.96 * SE,
    upper = mean + 1.96 * SE,
    "95%CI" = paste0(round(lower, 2), ", ", round(upper, 2))
  ) |>
  mutate(
    country = case_when(
      country == "Croatia" ~ "Хърватия",
      country == "Cyprus" ~ "Кипър",
      country == "Czech Republic" ~ "Чехия",
      country == "Denmark" ~ "Дания",
      country == "Finland" ~ "Финландия",
      country == "France" ~ "Франция",
      country == "Germany" ~ "Германия",
      country == "Greece" ~ "Гърция",
      country == "Ireland" ~ "Ирландия",
      country == "Italy" ~ "Италия",
      country == "Austria" ~ "Австрия",
      country == "Latvia" ~ "Латвия",
      country == "Lithuania" ~ "Литва",
      country == "Netherlands" ~ "Холандия",
      country == "Norway" ~ "Норвегия",
      country == "Poland" ~ "Полша",
      country == "Portugal" ~ "Португалия",
      country == "Slovakia" ~ "Словакия",
      country == "Slovenia" ~ "Словения",
      country == "Spain" ~ "Испания",
      country == "UK" ~ "Великобритания",
      country == "Belgium" ~ "Белгия",
      country == "Bulgaria" ~ "България",
      country == "Estonia" ~ "Естония",
      country == "Hungary" ~ "Унгария",
      country == "Malta" ~ "Малта",
      country == "Sweden" ~ "Швеция",
      country == "Switzerland" ~ "Швейцария"
    )
  ) |>
  mutate(variable =
           case_when(
             variable ==        "eucbp_addressing_unhealthy_diets_obesity_and_physical_inactivity" ~ "↓ Карциногенните в храните",
             variable == 
               "eucbp_adoption_of_a_new_occupational_safety_and_health_strategic_framework" ~
               "↓ Експозицията към химическо замърсяване на работа",
             variable == "eucbp_alignment_of_the_e_us_air_quality_standards_more_closely_with_the_who_guidelines" ~ 
               "≃ Стандартите за КАВ в ЕС със СЗО",
             variable == "eucbp_creation_of_a_knowledge_centre" ~ "Център за координация на ракови инициативи",  
             variable == "eucbp_creation_of_a_tobacco_free_generation" ~ "↑ Регулацията на тютюневите изделия в ЕС", 
             variable == "eucbp_developing_a_new_eu_cancer_screening_scheme" ~ 
               "↑ Достъп до скрининг за КРК, РМЖ, РШМ",
             variable == "eucbp_elimination_of_cancers_caused_by_human_papillomaviruses_vaccination" ~ 
               "↑ Ваксинацията срещу HPV",
             variable == "eucbp_enabling_cancer_patients_to_securely_access_and_share_electronic_health_records" ~ 
               "Споделяне на ЕЗЗ през ЕЗДП", 
             variable == "eucbp_improvement_of_health_literacy_on_cancer_risk_by_updating_the_european_code" ~ 
               "⟲ Европейския раков кодекс",
             variable == "eucbp_reducing_the_harmful_alcohol_consumption"  ~
               "↓ Злоупотребата с алкохол")) |> 
  mutate_round() |> 
  dplyr::select(country, n, variable, mean, "95%CI") |>
  knitr::kable()
  


eucbp_imp_models <- 
  pp |> 
  rowwise() |>
  mutate(
    eurecpp = sum(across(c(77:86))),
    ncrsum = sum(across(c(52:63))),
         cvpsum = sum(
           c(
             cpv_knowledge,
             cpv_perception,
             cpv_attitude,
             cpv_communication,
             cpv_reach,
             cpv_impact
           ))) |> 
  ungroup() |> 
  dplyr::select(-c(2,
                   38:44,
                   46:63,
                   71:87,
                   82)) |> 
 collect_model_results(outcome_var = "eurecpp")



eucbp_imp_models |> 
  mutate_if(is.numeric, round, 2) |>
  filter(model_p_value < 0.05) |>
  dplyr::select(1,2,3,6,7,8,9,10) |>
  dplyr::select(-term) |> 
  mutate(
    "95%CI" = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
    p.value = case_when(
      p.value < 0.01 ~ "<.001",
      p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(p.value)
    )) |> 
  dplyr::select(1,2,7,3,8) |> 
  knitr::kable()
  
## Clinical management ##


cm <-
  eu |>
  rowwise() |>
  mutate(
    eurecpp = sum(across(c(91:100))),
    ncrsum = sum(across(c(66:77))),
    cppsum = sum(across(c(60:65))),
    ncpsum = sum(across(c(44:51)))
  ) |>
  ungroup() |>
  select(-c(91:100, 66:77, 60:65, 44:51)) |>
  select(-c(1:4, 14, 22, 107:136)) |>
  rename_with(
    ~ gsub(
      "^usability_of_the_available_treatment_guidelines_",
      "gdl_",
      .
    ),
    starts_with("usability_of_the_available_treatment_guidelines_")
  ) |>
  rename_with(
    ~ gsub("^effectiveness_collaboration_", "collab_", .),
    starts_with("effectiveness_collaboration_")
  ) |>
  rename_with(
    ~ gsub("^reimbursement_new_therapies_importance_", "rmbfac_", .),
    starts_with("reimbursement_new_therapies_importance_")
  ) |>
  rename_with(
    ~ gsub("^effectiveness_of_the_clinical_trials_", "rct_", .),
    starts_with("effectiveness_of_the_clinical_trials_")
  ) |> 
  rename_with(
    ~ gsub("^eu_cancer_plan_recommendations_", "eucbptr_", .),
    starts_with("eu_cancer_plan_recommendations_")
  ) |> 
  rename_with(
  ~ gsub("^inovate_therapy_funding_", "itreat_fund_", .),
  starts_with("inovate_therapy_funding_")
)

 
  
cm |> 
  col_n_sum(59) |> 
  mutate(
    evidence_based_treatment_guidelines_for_rare_tumors_available =
      as_factor(evidence_based_treatment_guidelines_for_rare_tumors_available)
  ) |> 
  pcit() |> 
  compare_proportions() |> 
  mutate_round()

cm |>
  select(-c(2,60:100)) |>
  collect_model_results(outcome_var = "evidence_based_treatment_guidelines_for_rare_tumors_available") |>
  filter(model_p_value < 0.05 & p.value < 0.045) |>
  mutate_if(is.numeric, round, 2) 


cm |> 
  dplyr::select(starts_with("gdl_")) |>
  pivot_longer(cols = 1:7,
               names_to = "variable",
               values_to = "value") |>
  mutate(variable =
           case_when(
             variable == "gdl_cost_effectivness"  ~ "Разходна ефективност", 
             variable == "gdl_efficacy" ~ "Клинична ефективност",           
             variable == "gdl_evidence_base" ~ "Доказателствена основа", 
             variable == "gdl_feasibility" ~ "Приложимост",         
             variable ==  "gdl_novelty"  ~ "Съвременни",           
             variable == "gdl_patient_centerdness" ~ "Пациент-центрираност", 
             variable ==  "gdl_safety" ~ "Безопасност")) |>             
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(specs = "variable") |>
  tidy() |>
  ggplot(aes(x = estimate, y = fct_reorder(variable, estimate))) +
  geom_point(size = 3) +
  geom_rangeframe(data = tibble(
    variable = c(
      "Безопасност",            
      "Доказателствена основа", 
      "Клинична ефективност",  
      "Пациент-центрираност",
      "Приложимост",            
      "Разходна ефективност",  
      "Съвременни"),                 
    estimate = c(1, 5, 1, 
                 1, 1, 1,
                 1))
  )+
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.2f", estimate
    ))),
    hjust = +0.5,
    vjust = -0.52,
    size = 5,
    family = "Sofia Sans Condensed",
  ) +
  geom_errorbar(
    aes(
      xmin = estimate - 1.96 * std.error,
      xmax = estimate + 1.96 * std.error
    ),
    width = 0.2,
    alpha = 0.7,
    size = 0.5,
  ) +
  geom_vline(
    xintercept = 3.95,
    lty = 2,
    size = 0.5,
    color = "gray10"
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(1, 5.5),
    breaks = c(seq(1, 5, 1))
  ) +
  theme(legend.position = "none") +
  labs(x = "", y = "", subtitle = "")




# ggsave(
#   "mean-gdl-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 20,
#   height = 12
# )


cm |>
  dplyr::select(starts_with("gdl_")) |>
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
    Parameter1 =
      case_when(
        Parameter1 == "gdl_cost_effectivness"  ~ "Разходна ефективност",
        Parameter1 == "gdl_efficacy" ~ "Ефективност",
        Parameter1 == "gdl_evidence_base" ~ "Основани на доказателства",
        Parameter1 == "gdl_feasibility" ~ "Приложими",
        Parameter1 ==  "gdl_novelty"  ~ "Съвременни",
        Parameter1 == "gdl_patient_centerdness" ~ "Пациент-центрирани",
        Parameter1 ==  "gdl_safety" ~ "Безопасни"
      ),
    Parameter2 =
      case_when(
        Parameter2 == "gdl_cost_effectivness"  ~ "Разходна ефективност",
        Parameter2 == "gdl_efficacy" ~ "Ефективност",
        Parameter2 == "gdl_evidence_base" ~ "Основани на доказателства",
        Parameter2 == "gdl_feasibility" ~ "Приложими",
        Parameter2 ==  "gdl_novelty"  ~ "Съвременни",
        Parameter2 == "gdl_patient_centerdness" ~ "Пациент-центрирани",
        Parameter2 ==  "gdl_safety" ~ "Безопасни"
      ),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 45, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
      # legend.justification = c(1, 0),
      # legend.position = c(0.6, 0.7),
      legend.direction = "vertical")+
  labs(x = "", y = "", subtitle = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))


# ggsave(
#   "gdl-criteria-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 25,
#   height = 14
# )


cm |> 
  dplyr::select(starts_with("gdl_")) |>
  pivot_longer(cols = 1:7,
               names_to = "variable",
               values_to = "value") |>
  mutate(variable =
           case_when(
             variable == "gdl_cost_effectivness"  ~ "Разходна ефективност", 
             variable == "gdl_efficacy" ~ "Ефективност",           
             variable == "gdl_evidence_base" ~ "Доказателствена основа", 
             variable == "gdl_feasibility" ~ "Приложимост",         
             variable ==  "gdl_novelty"  ~ "Съвременност",           
             variable == "gdl_patient_centerdness" ~ "Пациент-центрираност", 
             variable ==  "gdl_safety" ~ "Безопасност")) |>             
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(specs = "variable") |>
  pairs(adjust = "bonferroni") |>
  tidy() |> 
  separate(contrast, into = c("FV", "SV"), sep = " - ", remove = FALSE)  |> 
  mutate(
    FV = gsub("[()]", "", FV),
    SV = gsub("[()]", "", SV)
  ) |> 
  dplyr::select(3,4,6,7,10) |> 
  mutate_round() |>
  mutate(
    lower = estimate - 1.96 * std.error,
    upper = estimate + 1.96 * std.error,
    CI = paste0(round(lower, 2), ", ", round(upper, 2)),
    adj.p.value = case_when(
      adj.p.value < 0.01 ~ "<.01",
      adj.p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(adj.p.value)
    )
  ) |>
  select(1,2,3,8,5) |> 
  knitr::kable()
  

gdl_models <-
  cm |>
  pivot_longer(cols = starts_with("gdl_"),
               names_to = "variable",
               values_to = "value") |>
  mutate(
    variable =
      case_when(
        variable == "gdl_cost_effectivness"  ~ "Разходна ефективност",
        variable == "gdl_efficacy" ~ "Ефективност",
        variable == "gdl_evidence_base" ~ "Доказателствена основа",
        variable == "gdl_feasibility" ~ "Приложимост",
        variable ==  "gdl_novelty"  ~ "Съвременност",
        variable == "gdl_patient_centerdness" ~ "Пациент-центрираност",
        variable ==  "gdl_safety" ~ "Безопасност"
      )
  ) |>
  select(-c(2, 60:93, 95)) |>
  group_by(variable) |>
  nest() |>
  mutate(
    models = map(data,~.x |>
          to_dummmy() |>
          collect_model_results(outcome_var = "value")
      )
  )
  

gdl_models |> 
  unnest(models) |>
  mutate_if(is.numeric, round, 2) |>
  dplyr::select(-data) |>
  filter(model_p_value < 0.05 & p.value < 0.049) |>
  dplyr::select(1,2,3,4,7,8,9,10) |>
  dplyr::select(-term) |> 
  mutate(
    "95%CI" = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
    p.value = case_when(
                       p.value < 0.01 ~ "<.01",
                       p.value > 0.90 ~ "> .90",
                       TRUE ~ as.character(p.value)
                     )) |> 
  dplyr::select(1,2,3,7,4,8) |> 
  flextable::flextable() 


#oncology_diff <- 
#  cm |>
#  select(specialty_oncology, starts_with("gdl_")) |> 
#  rsample::bootstraps(1000) |>
#  mutate(
#      diff = map(splits, ~ analysis(.x) |>
#                   pivot_longer(cols = starts_with("gdl_"),
#                                names_to = "variable",
#                                values_to = "value") |>
#                   group_by(specialty_oncology, variable) |> 
#                   summarise(mean = mean(value, na.rm = TRUE),
#                             .groups = "keep"))) 
#
#  

#  oncology_diff |>
#    unnest(diff) |>
#    pivot_wider(names_from = specialty_oncology, values_from = mean) |>
#    mutate(diff = `1` - `0`) |>
#    ungroup() |>
#    select(-c(splits, id)) |>
#    mutate(
#      variable =
#        case_when(
#          variable == "gdl_cost_effectivness"  ~ "Разходна ефективност",
#          variable == "gdl_efficacy" ~ "Клинична ефективност",
#          variable == "gdl_evidence_base" ~ "Доказателствена основа",
#          variable == "gdl_feasibility" ~ "Приложимост",
#          variable ==  "gdl_novelty"  ~ "Съвременност",
#          variable == "gdl_patient_centerdness" ~ "Пациент-центрираност",
#          variable ==  "gdl_safety" ~ "Безопасност"
#        )
#    ) |>
#      ggplot(aes(diff, 
#                 fct_reorder(variable, diff))) +
#      geom_rangeframe(
#        data = tibble(
#          variable = c(
#            "Безопасност",
#            "Доказателствена основа",
#            "Клинична ефективност",
#            "Пациент-центрираност",
#            "Приложимост",
#            "Разходна ефективност",
#            "Съвременност"
#          ),
#          diff = c(1.5, -1.5, 0, 1, 1, 1, 1)
#        )
#        )+
#    stat_halfeye(aes(fill_ramp = after_stat(x > 0)), fill = "#37B7C3") +
#    geom_vline(xintercept = 0) +
#    scale_fill_ramp_discrete(from = "#174E53", guide = "none") +
#    scale_x_continuous(expand = c(0, 0),
#                       limits = c(-1.5, 2), 
#                       breaks = c(seq(-1.5, 1.5, 0.5))) +
#    theme(legend.position = "none") +
#    labs(x = "Δ Онколози vs. Други", y = "", subtitle = "") 
#  
#  ggsave(
#    "oncology-gdl-diff-bg.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 25,
#    height = 14
#  )

cm |> 
  select(starts_with("collab_")) |>
  pivot_longer(cols = 1:6,
               names_to = "variable",
               values_to = "value") |>
  mutate(variable =
           case_when(
             variable == "collab_accessibility" ~ "Достъпност",
             variable =="collab_communication" ~ "Комуникация",           
             variable =="collab_expertise" ~ "Експертиза",                
             variable =="collab_improvement" ~ "Подобрение",              
             variable =="collab_interdisciplinary_approach" ~ "Интердисциплинарност",
             variable == "collab_shared_decision_making" ~ "Споделено решение")) |>            
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(specs = "variable") |>
  tidy() |>
  ggplot(aes(x = estimate, y = fct_reorder(variable, estimate))) +
  geom_point(size = 3) +
  geom_rangeframe(data = tibble(
    variable = c(
      "Достъпност",
      "Експертиза",
      "Интердисциплинарност",
      "Комуникация",          
      "Подобрение",           
      "Споделено решение"),                 
    estimate = c(1, 5, 1, 
                 1, 1, 1))
  )+
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.2f", estimate
    ))),
    hjust = +0.5,
    vjust = -0.52,
    size = 6,
    family = "Sofia Sans Condensed",
  ) +
  geom_errorbar(
    aes(
      xmin = estimate - 1.96 * std.error,
      xmax = estimate + 1.96 * std.error
    ),
    width = 0.2,
    alpha = 0.7,
    size = 0.5,
  ) +
  geom_vline(
    xintercept = 3.95,
    lty = 2,
    size = 0.5,
    color = "gray10"
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(1, 5.5),
    breaks = c(seq(1, 5, 1))
  ) +
  theme(legend.position = "none") +
  labs(x = "", y = "", subtitle = "")
 
#  ggsave(
#    "mean-collab-bg.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 20,
#    height = 12
#  )



cm |> 
  select(starts_with("collab_")) |>
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
    Parameter1 =
      case_when(
        Parameter1 == "collab_accessibility" ~ "Достъпност",
        Parameter1 == "collab_communication" ~ "Комуникация",
        Parameter1 == "collab_expertise" ~ "Експертиза",
        Parameter1 == "collab_improvement" ~ "Подобрение",
        Parameter1 == "collab_interdisciplinary_approach" ~ "Интердисциплинарност",
        Parameter1 == "collab_shared_decision_making" ~ "Споделено решение"
      ),
    Parameter2 =
      case_when(
        Parameter2 == "collab_accessibility" ~ "Достъпност",
        Parameter2 == "collab_communication" ~ "Комуникация",
        Parameter2 == "collab_expertise" ~ "Експертиза",
        Parameter2 == "collab_improvement" ~ "Подобрение",
        Parameter2 == "collab_interdisciplinary_approach" ~ "Интердисциплинарност",
        Parameter2 == "collab_shared_decision_making" ~ "Споделено решение"
      ),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 45, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "", subtitle = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))


# ggsave(
#   "collab-full-criteria-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 25,
#   height = 14
# )

 
cm |>
  count(collab_communication, collab_accessibility) |>
  full_join(expand.grid(collab_communication = 1:5, collab_accessibility = 1:5)) |>
  mutate(n = ifelse(is.na(n), 0, n),
         sum = sum(n),
         prop = n / sum) |>
  ggplot(aes(x = collab_accessibility, y = collab_communication)) +
  geom_tile(
    aes(fill = prop),
    color = "white",
    alpha = 0.9,
    linewidth = 1
  ) +
  geom_text(
    aes(label = ifelse(prop > 0,
                       paste0("  ", sprintf(
                         "%2.1f", prop * 100
                       ), "%  "),
                       ""
    )),
    vjust = 0.5,
    hjust = 0.5,
    size = 5,
    family = "Roboto Condensed",
  ) +
  geom_rangeframe(data = tibble(
    collab_communication = c(1, 2, 3, 4, 5),
    collab_accessibility = c(1, 2, 3, 4, 5)
  )) +
  scale_fill_gradient2(
    midpoint = 0.12,
    low = "white",
    mid = "#31B1C2",
    high = "#021526"
  ) +
  theme(legend.position = "none") +
  labs(x = "Достъпност", y = "Комуникация")

# ggsave(
#   "collab-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 22,
#   height = 14
# )

cm |> 
  select(starts_with("collab_")) |>
  pivot_longer(cols = 1:6,
               names_to = "variable",
               values_to = "value") |>
  mutate(variable =
           case_when(
             variable == "collab_accessibility" ~ "Достъпност",
             variable =="collab_communication" ~ "Комуникация",           
             variable =="collab_expertise" ~ "Експертиза",                
             variable =="collab_improvement" ~ "Подобрение",              
             variable =="collab_interdisciplinary_approach" ~ "Интердисциплинарност",
             variable == "collab_shared_decision_making" ~ "Споделено решение")) |>            
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(specs = "variable") |>
  pairs(adjust = "bonferroni") |>
  tidy() |>
  separate(contrast, into = c("FV", "SV"), sep = " - ", remove = FALSE)  |>
  mutate(
    FV = gsub("[()]", "", FV),
    SV = gsub("[()]", "", SV)
  ) |>
  dplyr::select(3,4,6,7,10) |>
  mutate_round() |>
  mutate(
    lower = estimate - 1.96 * std.error,
    upper = estimate + 1.96 * std.error,
    CI = paste0(round(lower, 2), ", ", round(upper, 2)),
    adj.p.value = case_when(
      adj.p.value < 0.01 ~ "<.01",
      adj.p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(adj.p.value)
    )
  ) |>
  select(1,2,3,8,5) |>
  knitr::kable()


cm |> 
  select(country, starts_with("collab_")) |>
  pivot_longer(cols = 2:7,
               names_to = "variable",
               values_to = "value") |>
  mutate(variable =
           case_when(
             variable == "collab_accessibility" ~ "Достъпност",
             variable =="collab_communication" ~ "Комуникация",           
             variable =="collab_expertise" ~ "Експертиза",                
             variable =="collab_improvement" ~ "Подобрение",              
             variable =="collab_interdisciplinary_approach" ~ "Интердисциплинарност",
             variable == "collab_shared_decision_making" ~ "Споделено решение")) |> 
  mutate(
    country = case_when(
      country == "Croatia" ~ "Хърватия",
      country == "Cyprus" ~ "Кипър",
      country == "Czech Republic" ~ "Чехия",
      country == "Denmark" ~ "Дания",
      country == "Finland" ~ "Финландия",
      country == "France" ~ "Франция",
      country == "Germany" ~ "Германия",
      country == "Greece" ~ "Гърция",
      country == "Ireland" ~ "Ирландия",
      country == "Italy" ~ "Италия",
      country == "Austria" ~ "Австрия",
      country == "Latvia" ~ "Латвия",
      country == "Lithuania" ~ "Литва",
      country == "Netherlands" ~ "Холандия",
      country == "Norway" ~ "Норвегия",
      country == "Poland" ~ "Полша",
      country == "Portugal" ~ "Португалия",
      country == "Slovakia" ~ "Словакия",
      country == "Slovenia" ~ "Словения",
      country == "Spain" ~ "Испания",
      country == "UK" ~ "Великобритания",
      country == "Belgium" ~ "Белгия",
      country == "Bulgaria" ~ "България",
      country == "Estonia" ~ "Естония",
      country == "Hungary" ~ "Унгария",
      country == "Malta" ~ "Малта",
      country == "Sweden" ~ "Швеция",
      country == "Switzerland" ~ "Швейцария"
    )
  ) |>
 group_by(country,variable) |> 
 summarise(
   mean = mean(value, na.rm = TRUE),
   sd = sd(value, na.rm = TRUE),
   se = sd(value, na.rm = TRUE) / sqrt(n()),
   "95%CI" = paste0(round(mean - 1.96 * se, 2), ", ", round(mean + 1.96 * se, 2))) |> 
  mutate_round() |> 
  select(2,1,3,6) |>
  ungroup() |>
  group_by(variable) |> 
  arrange(-mean, .by_group = T) |> 
  knitr::kable()


collab_models <-
  cm |>
  pivot_longer(cols = starts_with("collab_"),
               names_to = "variable",
               values_to = "value") |>
  mutate(
    variable =
      case_when(
        variable == "collab_accessibility" ~ "Достъпност",
        variable == "collab_communication" ~ "Комуникация",
        variable == "collab_expertise" ~ "Експертиза",
        variable == "collab_improvement" ~ "Подобрение",
        variable == "collab_interdisciplinary_approach" ~ "Интердисциплинарност",
        variable == "collab_shared_decision_making" ~ "Споделено решение"
      )
    )|> 
  select(-c(2, 67:94, 96)) |>
  mutate(
    hcepc = log(hcepc),
  ) |> 
  group_by(variable) |>
  nest() |>
  mutate(
    models = map(data,~.x |>
                   to_dummmy() |>
                   collect_model_results(outcome_var = "value")
    )
  )


collab_models |> 
  unnest(models) |>
  mutate_if(is.numeric, round, 2) |>
  dplyr::select(-data) |>
  filter(model_p_value < 0.05 & p.value < 0.049) |>
  dplyr::select(1,2,3,4,7,8,9,10) |>
  dplyr::select(-term) |>
  mutate(
    "95%CI" = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
    p.value = case_when(
      p.value < 0.01 ~ "<.01",
      p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(p.value)
    )) |> 
  dplyr::select(1,2,3,7,4,8) |> 
  flextable::flextable() 



cm |>
  select(73:77) |>
  pivot_longer(cols = 1:5,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    variable =
      case_when(
        variable == "rmbfac_disease_severity_clinical_burden" ~ "Тежест на заболяването",
        variable == "rmbfac_strength_robustness_quality_of_evidence" ~ "Качество на научните данни",
        variable == "rmbfac_therapeutic_value" ~ "Терапевтична ефективност",
        variable == "rmbfac_unmet_need_lack_of_active_treatment_alternatives" ~ "Липса на алтернативи",
        variable == "rmbfac_value_for_money_and_budget_impact" ~ "Разходи и бюджетно въздействие"
      )
  ) |>
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(specs = "variable") |>
  pairs(adjust = "bonferroni") |>
  tidy() |>
  separate(contrast, 
           into = c("FV", "SV"), 
           sep = " - ", 
           remove = T)  |> 
  dplyr::select(2,3,5,6,9) |> 
  mutate_if(is.numeric, round, 2) |>
  mutate(
    lower = estimate - 1.96 * std.error,
    upper = estimate + 1.96 * std.error,
    CI = paste0(round(lower, 2), ", ", round(upper, 2)),
    adj.p.value = case_when(
       adj.p.value < 0.01 ~ "<.01",
      adj.p.value > 0.90 ~ "> .90",
  TRUE ~ as.character(adj.p.value))
        ) |> 
  select(1,2,3,8,5) |>
  knitr::kable()
  





  
  cm |> 
    select(94:100) |> 
    pivot_longer(cols = 1:7,
                 names_to = "variable",
                 values_to = "value") |>
    mutate(variable = 
             case_when(
               variable == "itreat_fund_other_eu_financing_project_lines"  ~ "Програми и фондове на ЕС",
               variable == "itreat_fund_other_industry"   ~ "Индустрия",                     
               variable == "itreat_fund_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
               variable == "itreat_fund_private_household_out_of_pocket_expenditure"  ~ "Лични разходи на домакинствата",   
               variable == "itreat_fund_private_voluntary_health_insurance_funding" ~ "ДОФ", 
               variable == "itreat_fund_public_goverment_funding" ~ "Държавно финансиране",  
               variable == "itreat_fund_public_health_insurance_funding" ~ "Задължителни ЗОФ"
             )) |>            
    aov(value ~ variable, data = _) |>
    emmeans::emmeans(specs = "variable") |> 
    pairs(adjust = "bonferroni") |>
    tidy() |>
    separate(contrast, 
             into = c("FV", "SV"), 
             sep = " - ", 
             remove = T)  |> 
    dplyr::select(2,3,5,6,9) |> 
    mutate_if(is.numeric, round, 2) |>
    mutate(
      lower = estimate - 1.96 * std.error,
      upper = estimate + 1.96 * std.error,
      CI = paste0(round(lower, 2), ", ", round(upper, 2)),
      adj.p.value = case_when(
        adj.p.value < 0.01 ~ "<.01",
        adj.p.value > 0.90 ~ "> .90",
        TRUE ~ as.character(adj.p.value))
    ) |> 
    select(1,2,3,8,5) |>
    knitr::kable()
  

country_comp <- 
  cm |> 
    select(hcepc_hight, 94:100, 73:77) |> 
    pivot_longer(cols = 2:13,
                 names_to = "variable",
                 values_to = "value") |>
    separate(
      variable,
      into = c("category", "variable"),
      sep = "_",
      extra = "merge",
      remove = T
    ) |>
  mutate(variable = case_when(
    variable == "fund_other_eu_financing_project_lines"  ~ "Програми и фондове на ЕС",
    variable == "fund_other_industry" ~ "Индустрия",                  
    variable == "fund_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
    variable == "fund_private_household_out_of_pocket_expenditure"  ~ "Лични разходи",   
    variable == "fund_private_voluntary_health_insurance_funding" ~ "ДОФ", 
    variable == "fund_public_goverment_funding" ~ "Държавно финансиране",
    variable == "fund_public_health_insurance_funding" ~ "Задължителни ЗОФ",
    variable == "disease_severity_clinical_burden" ~ "Тежест на заболяването",
    variable == "strength_robustness_quality_of_evidence" ~ "Качество на научните данни",
    variable == "therapeutic_value" ~ "Терапевтична ефективност",
    variable == "unmet_need_lack_of_active_treatment_alternatives" ~ "Липса на алтернативи",
    variable == "value_for_money_and_budget_impact" ~ "Разходи и бюджетно въздействие")) |> 
  group_by(category,variable) |> 
  nest() |>
  mutate(
    comp = map(data,~.x |>
                   aov(value ~ hcepc_hight, data = _) |>  
                   emmeans::emmeans(specs = "hcepc_hight") |>
                        pairs(adjust = "Bonferroni", reverse = TRUE) |>
                 tidy()))
 
country_comp |>    
  unnest(comp) |>
  select(-data) |> 
  mutate_round() |> 
  select(2,6,7,9,10) |> 
  mutate(
    lower = estimate - 1.96 * std.error,
    upper = estimate + 1.96 * std.error,
    CI = paste0(round(lower, 2), ", ", round(upper, 2)),
    p.value = case_when(
      p.value < 0.01 ~ "<.01",
      p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(p.value)
    )) |> 
  ungroup() |> 
  select(2,3,6,9) |> 
  arrange(estimate) |>
  knitr::kable()

 
  country_comp |>    
  unnest(comp) |>
  select(-data) |> 
  mutate_round() |> 
  mutate(
    lci = estimate - 1.96 * std.error,
    uci = estimate + 1.96 * std.error,
    CI = paste0(round(lci, 2), ", ", round(uci, 2)),
    p.value = case_when(
      p.value < 0.001 ~ "***",
      p.value < 0.01 ~ "**",
      p.value < 0.05 ~ "*",
      TRUE ~ ""
    )) |>
    ggplot(aes(
      x = estimate,
      y = fct_reorder(variable, estimate)
    )) +
    geom_point(size = 3) +
    geom_errorbar(
      aes(
        xmin = lci,
        xmax = uci
      ),
      width = 0.2,
      alpha = 0.7,
      size = 0.5
    ) +
    geom_vline(
      xintercept = 0,
      lty = 2,
      size = 0.5,
      color = "gray10"
    ) +
    geom_text(
      aes(label = paste0("  ", sprintf(
        "%2.2f", estimate), p.value)),
      hjust = +0.5,
      vjust = -0.52,
      size = 6,
      family = "Sofia Sans Condensed",
    ) +
    scale_x_continuous(
      breaks = c(seq(-1.5, 1.5, 1)),
      limits = c(-1.5, 2.5),
      expand = c(0, 0)
    )+
    facet_wrap(~category, 
               scales = "free",
               labeller = labeller(category = c(
                 itreat = "Източник",
                 rmbfac = "Фактор")))+
    guides(
      x = guide_axis(cap = "both"), # Cap both ends
      y = guide_axis(cap = "both") # Cap the upper end
    ) +
    theme(axis.line = element_line())+
    labs(x = "Δ (95%CI) Държави с високи - Държави с ниски ПРЗГН", 
         y = "")
  
# ggsave(
#   "hcepc-fact-sources-th-comp-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 32,
#   height = 12
# )

  

t_remb_fact <- 
  cm |> 
  select(73:77) |> 
  pivot_longer(cols = 1:5,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    fct_var = case_when(
      value == 1 ~ "no",
      value == 2 ~ "no",
      value == 3 ~ "both",
      value == 4 ~ "yes",
      value == 5 ~ "yes"
    )
  ) |>
  count(variable, fct_var) |>
  group_by(variable) |>
  pivot_wider(names_from = fct_var, values_from = n) |>
  mutate(
    agreement = (yes + 0.5 * both) / 92,
    disagreement = (no + 0.5 * both) / 92,
    adr = agreement / disagreement,
    adr1 = ifelse(adr > 1, TRUE, FALSE)
  ) |>
  dplyr::select(variable, agreement, disagreement, adr, adr1) |>
  ggplot(aes(
    x = agreement,
    y = fct_reorder(variable, agreement),
    fill = adr1
  )) +
  geom_col(color = "gray10", alpha = 0.7) +
  geom_vline(
    xintercept = 0.5,
    lty = 2,
    size = 0.5,
    color = "#013440"
  ) +
  geom_rangeframe(data = tibble(
    variable = c(
      "rmbfac_disease_severity_clinical_burden",                
      "rmbfac_value_for_money_and_budget_impact",               
      "rmbfac_unmet_need_lack_of_active_treatment_alternatives",
      "rmbfac_strength_robustness_quality_of_evidence",         
      "rmbfac_therapeutic_value"  
    ),
    agreement = c(0, 1, 0, 0, 0),
    adr1 = c(FALSE, FALSE, FALSE, TRUE, FALSE)
  )) +
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.1f", agreement * 100
    ), "%  ")),
    #color = agreement > .05
    #hjust = agreement > .05),
    hjust = "right",
    size = 5,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  scale_fill_manual(values = generate_palette("#37B7C3", 
                                              modification = "go_both_ways", 
                                              n_colours = 2))+
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(-0.05, 1.1),
    breaks = c(seq(0, 1, 0.2)),
    labels = scales::label_percent()
  ) +
  scale_y_discrete(
    labels = c(
      "rmbfac_disease_severity_clinical_burden" = "Тежест на заболяването",                
      "rmbfac_value_for_money_and_budget_impact" = "Разходи и бюджетно въздействие",               
      "rmbfac_unmet_need_lack_of_active_treatment_alternatives" = "Липса на алтернативи",
      "rmbfac_strength_robustness_quality_of_evidence" = "Качество на научните данни",         
      "rmbfac_therapeutic_value" = "Терапевтична ефективност"
    )
  ) +
  theme(legend.position = "none",
        axis.text = element_text(
          family = "Sofia Sans Condensed", 
          size = 20)) +
  labs(y = "", x = "%Одобрение")

t_remb_sources <- 
cm |> 
  select(94:100) |> 
  pivot_longer(cols = 1:7,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    fct_var = case_when(
      value == 1 ~ "no",
      value == 2 ~ "no",
      value == 3 ~ "both",
      value == 4 ~ "yes",
      value == 5 ~ "yes"
    )
  ) |>
  count(variable, fct_var) |>
  group_by(variable) |>
  pivot_wider(names_from = fct_var, values_from = n) |>
  mutate(
    agreement = (yes + 0.5 * both) / 92,
    disagreement = (no + 0.5 * both) / 92,
    adr = agreement / disagreement,
    adr1 = ifelse(adr > 1, TRUE, FALSE)
  ) |>
  dplyr::select(variable, agreement, disagreement, adr, adr1) |>
  ggplot(aes(
    x = agreement,
    y = fct_reorder(variable, agreement),
    fill = adr1
  )) +
  geom_col(color = "gray10", alpha = 0.7) +
  geom_vline(
    xintercept = 0.5,
    lty = 2,
    size = 0.5,
    color = "#013440"
  ) +
  geom_rangeframe(data = tibble(
    variable = c(
      "itreat_fund_other_eu_financing_project_lines",                
      "itreat_fund_other_industry",                                  
      "itreat_fund_other_non_profit_institutions_serving_households",
      "itreat_fund_private_household_out_of_pocket_expenditure",     
      "itreat_fund_private_voluntary_health_insurance_funding",      
      "itreat_fund_public_goverment_funding",                        
      "itreat_fund_public_health_insurance_funding" 
    ),
    agreement = c(0, 1, 0, 
                  0, 1, 0, 
                  1),
    adr1 = c(FALSE, FALSE, FALSE, 
             FALSE, FALSE, FALSE, 
             TRUE)
  )) +
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.1f", agreement * 100
    ), "%  ")),
    #color = agreement > .05
    #hjust = agreement > .05),
    hjust = "right",
    size = 5,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  scale_fill_manual(values = generate_palette("#37B7C3", 
                                              modification = "go_both_ways", 
                                              n_colours = 2))+
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(-0.05, 1.1),
    breaks = c(seq(0, 1, 0.2)),
    labels = scales::label_percent()
  ) +
  scale_y_discrete(
    labels = c(
      "itreat_fund_other_eu_financing_project_lines"  = "Програми и фондове на ЕС",
      "itreat_fund_other_industry"   = "Индустрия",                     
      "itreat_fund_other_non_profit_institutions_serving_households" = "Финансиране от НПО",
      "itreat_fund_private_household_out_of_pocket_expenditure"  = "Лични разходи",   
      "itreat_fund_private_voluntary_health_insurance_funding" = "ДОФ", 
      "itreat_fund_public_goverment_funding" = "Държавно финансиране",  
      "itreat_fund_public_health_insurance_funding" = "Задължителни ЗОФ"
  )) +
  theme(legend.position = "none",
        axis.text = element_text(
          family = "Sofia Sans Condensed", 
          size = 20)) +
  labs(y = "", x = "%Одобрение")

t_remb_fact/t_remb_sources

# ggsave(
#   "therapy-fct-sources-bg.png",
#       bg = "white",
#       units = "cm",
#       dpi = 1000,
#       width = 21,
#       height = 22
# )

th_fund_fac_cor <- 
  cm |> 
  select(starts_with("rmbfac_")) |>
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
    Parameter1 =
      case_when(
        Parameter1 == "rmbfac_disease_severity_clinical_burden" ~ "Тежест на заболяването",                                     
         Parameter1 ==  "rmbfac_strength_robustness_quality_of_evidence" ~ "Качество на научните данни",             
         Parameter1 ==  "rmbfac_therapeutic_value"  ~ "Терапевтична ефективност",                                 
         Parameter1 ==  "rmbfac_unmet_need_lack_of_active_treatment_alternatives"  ~ "Липса на алтернативи",   
         Parameter1 ==  "rmbfac_value_for_money_and_budget_impact" ~ "Разходи и бюджетно въздействие"      
      ),
    Parameter2 =
      case_when(
        Parameter2 == "rmbfac_disease_severity_clinical_burden" ~ "Тежест на заболяването",                                     
        Parameter2 ==  "rmbfac_strength_robustness_quality_of_evidence" ~ "Качество на научните данни",             
        Parameter2 ==  "rmbfac_therapeutic_value"  ~ "Терапевтична ефективност",                                 
        Parameter2 ==  "rmbfac_unmet_need_lack_of_active_treatment_alternatives"  ~ "Липса на алтернативи",   
        Parameter2 ==  "rmbfac_value_for_money_and_budget_impact" ~ "Разходи и бюджетно въздействие"      
      ),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 40, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "", subtitle = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))+
  theme(
    axis.text = element_text(
          family = "Sofia Sans Condensed", 
          size = 20))



th_fund_source_cor <- 
  cm |> 
  select(starts_with("itreat_")) |>
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
    Parameter1 =
      case_when(
        Parameter1 == "itreat_fund_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",                
        Parameter1 == "itreat_fund_other_industry" ~ "Индустрия",     
        Parameter1 ==  "itreat_fund_other_non_profit_institutions_serving_households" ~ "НПО",  
        Parameter1 == "itreat_fund_private_household_out_of_pocket_expenditure" ~ "Лични разходи",    
        Parameter1 == "itreat_fund_private_voluntary_health_insurance_funding"   ~ "ДОФ",   
        Parameter1 == "itreat_fund_public_goverment_funding" ~ "Държавно финансиране",                       
                   Parameter1 == "itreat_fund_public_health_insurance_funding" ~ "ЗОФ"     
      ),
    Parameter2 =
      case_when(
        Parameter2 == "itreat_fund_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",                
        Parameter2 == "itreat_fund_other_industry" ~ "Индустрия",     
        Parameter2 ==  "itreat_fund_other_non_profit_institutions_serving_households" ~ "НПО",  
        Parameter2 == "itreat_fund_private_household_out_of_pocket_expenditure" ~ "Лични разходи",    
        Parameter2 == "itreat_fund_private_voluntary_health_insurance_funding"   ~ "ДОФ",   
        Parameter2 == "itreat_fund_public_goverment_funding" ~ "Държавно финансиране",                       
        Parameter2 == "itreat_fund_public_health_insurance_funding" ~ "ЗОФ"        
      ),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 40, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "", subtitle = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))+
  theme(axis.text = element_text(
    family = "Sofia Sans Condensed", 
    size = 20))

th_fund_fac_cor/th_fund_source_cor

# ggsave(
#   "th-fund-full-criteria-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 22,
#   height = 28
# )

  cm |> 
  select(starts_with("itreat_"), starts_with("rmbfac_")) |> 
  correlation(
    select = c(
    "itreat_fund_public_goverment_funding",
    "itreat_fund_public_health_insurance_funding",
    "itreat_fund_private_voluntary_health_insurance_funding",    
    "itreat_fund_private_household_out_of_pocket_expenditure",
    "itreat_fund_other_non_profit_institutions_serving_households",
    "itreat_fund_other_eu_financing_project_lines",
    "itreat_fund_other_industry"), 
    select2 = c(
      "rmbfac_disease_severity_clinical_burden",                     
      "rmbfac_value_for_money_and_budget_impact",                    
      "rmbfac_unmet_need_lack_of_active_treatment_alternatives",     
      "rmbfac_strength_robustness_quality_of_evidence",              
      "rmbfac_therapeutic_value" 
    )) |>
  tibble() |>
  mutate(
    Parameter1 =
          case_when(
            Parameter1 == "itreat_fund_other_eu_financing_project_lines" ~ "Програми и фондове на ЕС",                
            Parameter1 == "itreat_fund_other_industry" ~ "Индустрия",     
            Parameter1 ==  "itreat_fund_other_non_profit_institutions_serving_households" ~ "НПО",  
            Parameter1 == "itreat_fund_private_household_out_of_pocket_expenditure" ~ "Лични разходи",    
            Parameter1 == "itreat_fund_private_voluntary_health_insurance_funding"   ~ "ДОФ",   
            Parameter1 == "itreat_fund_public_goverment_funding" ~ "Държавно финансиране",                       
            Parameter1 == "itreat_fund_public_health_insurance_funding" ~ "ЗОФ"        
          ),
    Parameter2 =
      case_when(
        Parameter2 == "rmbfac_disease_severity_clinical_burden" ~ "Тежест на заболяването",                                     
        Parameter2 ==  "rmbfac_strength_robustness_quality_of_evidence" ~ "Качество на научните данни",             
        Parameter2 ==  "rmbfac_therapeutic_value"  ~ "Терапевтична ефективност",                                 
        Parameter2 ==  "rmbfac_unmet_need_lack_of_active_treatment_alternatives"  ~ "Липса на алтернативи",   
        Parameter2 ==  "rmbfac_value_for_money_and_budget_impact" ~ "Разходи и бюджетно въздействие"      
      ),
  p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 40, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "", subtitle = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))+
  theme(axis.text = element_text(
    family = "Sofia Sans Condensed", 
    size = 20))



# ggsave(
#   "th-fund-inter-full-criteria-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 22,
#   height = 14
# )
  
  
  
  
  
  fnd_models <- 
  cm |> 
  pivot_longer(cols = c(94:100, 73:77),
               names_to = "variable",
               values_to = "value") |>
  separate(
    variable,
    into = c("category", "variable"),
    sep = "_",
    extra = "merge",
    remove = T
  ) |>
  mutate(variable = case_when(
    variable == "fund_other_eu_financing_project_lines"  ~ "Програми и фондове на ЕС",
    variable == "fund_other_industry" ~ "Индустрия",                  
    variable == "fund_other_non_profit_institutions_serving_households" ~ "Финансиране от НПО",
    variable == "fund_private_household_out_of_pocket_expenditure"  ~ "Лични разходи",   
    variable == "fund_private_voluntary_health_insurance_funding" ~ "ДОФ", 
    variable == "fund_public_goverment_funding" ~ "Държавно финансиране",
    variable == "fund_public_health_insurance_funding" ~ "Задължителни ЗОФ",
    variable == "disease_severity_clinical_burden" ~ "Тежест на заболяването",
    variable == "strength_robustness_quality_of_evidence" ~ "Качество на научните данни",
    variable == "therapeutic_value" ~ "Терапевтична ефективност",
    variable == "unmet_need_lack_of_active_treatment_alternatives" ~ "Липса на алтернативи",
    variable == "value_for_money_and_budget_impact" ~ "Разходи и бюджетно въздействие")) |> 
  select(-c(2, 46:88, 91)) |>
  group_by(category,variable) |> 
  nest() |>
  mutate(
      models = map(data, ~
                     .x |> 
                     to_dummmy() |>
                     collect_model_results(outcome_var = "value")))
  
  
  fnd_models |>
  unnest(models) |>
  select(-data) |>
  mutate_if(is.numeric, round, 2) |>
  filter(model_p_value < 0.05 & p.value < 0.05) |> 
  ungroup() |>
  select(-category) |> 
  dplyr::select(1,2,3,4,7,8,9,10) |>
  dplyr::select(-term) |>
  mutate(
      "95%CI" = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
      p.value = case_when(
        p.value < 0.01 ~ "<.01",
        p.value > 0.90 ~ "> .90",
        TRUE ~ as.character(p.value)
      )) |> 
    dplyr::select(1,2,3,7,4,8) |> 
    flextable::flextable()  

  cm |>
    dplyr::select(78:82) |>
    get_summary_stats() |>
    ggplot(aes(x = mean, y = fct_reorder(variable, mean))) +
    geom_point(size = 3) +
    geom_text(
      aes(label = paste0("  ", sprintf(
        "%2.2f", mean
      ))),
      hjust = +0.5,
      vjust = -0.5,
      size = 6,
      family = "Sofia Sans Condensed"
    ) +
    geom_errorbar(
      aes(xmin = mean - 1.96 * se, xmax = mean + 1.96 * se),
      width = 0.2,
      size = 0.5,
      color = "gray10"
    ) +
    geom_vline(
      xintercept = 2.80,
      lty = 2,
      size = 0.5,
      color = "gray10"
    ) +
    scale_y_discrete(
      labels = c(
        rct_availability = "Наличност",
        rct_coverage = "Покритие",
        rct_inclusivity = "Включване",
        rct_affordability = "Достъпност",
        rct_contemporary = "Навременност"
                )
    )+
    scale_x_continuous(
      expand = c(0, 0),
      limits = c(1, 5.5),
      breaks = c(seq(1, 5, 1))
    ) +
    guides(
      x = guide_axis(cap = "both"), # Cap both ends
      y = guide_axis(cap = "both") # Cap the upper end
    ) +
    theme(axis.line = element_line(
      linewidth = 0.25,
      color = "black"
    ))+
    labs(x = "", y = "", subtitle = "")
  
# ggsave("rct-mean-bg.png",
#        device = "png",
#        bg = "white",
#        units = "mm",
#        width = 180,
#        height = 100,
#        dpi = 1000)
  
  cm |> 
    select(starts_with("rct_")) |>
    correlation(redundant = TRUE) |>
    tibble() |>
    mutate(
      Parameter1 =
        case_when(
          Parameter1 == "rct_availability" ~ "Наличност",
          Parameter1 == "rct_coverage" ~ "Покритие",
          Parameter1 == "rct_inclusivity" ~ "Включване",
          Parameter1 == "rct_affordability" ~ "Достъпност",
          Parameter1 == "rct_contemporary" ~ "Навременност"
        ),
      Parameter2 =
        case_when(
          Parameter2 == "rct_availability" ~ "Наличност",
          Parameter2 == "rct_coverage" ~ "Покритие",
          Parameter2 == "rct_inclusivity" ~ "Включване",
          Parameter2 == "rct_affordability" ~ "Достъпност",
          Parameter2 == "rct_contemporary" ~ "Навременност"
        ),
      p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
    ) |>
    filter(Parameter1 != Parameter2) |>
    filter(Parameter1 > Parameter2) |>
    ggplot(aes(Parameter1, Parameter2, fill = r)) +
    geom_tile(color = "white") +
    scale_fill_gradient2(
      low = "#4158A6",
      high = "#FF8343",
      mid = "white",
      midpoint = 0,
      limit = c(-1, 1),
      space = "Lab",
      name = ""
    ) +
    geom_text(aes(label = paste0(round(r, 2), 
                                 p_astr)), 
              color = "black", 
              family = "Sofia Sans Condensed",
              size = 5) +
    theme(axis.text.x = element_text(angle = 40, 
                                     vjust = 1, 
                                     hjust = 1)) +
    geom_rangeframe()+
    theme(
      # legend.justification = c(1, 0),
      # legend.position = c(0.6, 0.7),
      legend.direction = "vertical")+
    labs(x = "", y = "", subtitle = "") +
    guides(fill = guide_colorbar(barwidth = 1.5, 
                                 barheight = 12,
                                 title.hjust = 0.5))+
    theme(
      axis.text = element_text(
        family = "Sofia Sans Condensed", 
        size = 20))  
  
  
#  ggsave(
#    "rct-full-criteria-cor-bg.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 16,
#    height = 12
#  )

  
cm |> 
  select(starts_with("rct_")) |> 
  ltm::cronbach.alpha(standardized = T, CI = T)
  
cm |> 
  select(starts_with("rct_")) |> 
  psych::alpha()
  
cm |> 
  select(starts_with("rct_")) |> 
  psych::KMO()

cm |> 
  select(starts_with("rct_")) |> 
  psych::cortest.bartlett()

cm  |>
  rowwise() |>
  mutate(rctsum = sum(across(starts_with("rct_")))) |>
  ungroup() |>
  dplyr::select(-c(starts_with("rct_"))) |>
  get_summary_stats(rctsum)
  
  
cm  |>
  rowwise() |>
  mutate(rctsum = sum(across(starts_with("rct_")))) |>
  ungroup() |>
  aov(rctsum~ country, data = _) |>
  emmeans::emmeans(specs = "country") |>
  tidy() |>
  mutate_if(is.numeric, round, 2) |>
  select(1,2,3) |> 
  mutate(
    country = case_when(
      country == "Croatia" ~ "Хърватия",
      country == "Cyprus" ~ "Кипър",
      country == "Czech Republic" ~ "Чехия",
      country == "Denmark" ~ "Дания",
      country == "Finland" ~ "Финландия",
      country == "France" ~ "Франция",
      country == "Germany" ~ "Германия",
      country == "Greece" ~ "Гърция",
      country == "Ireland" ~ "Ирландия",
      country == "Italy" ~ "Италия",
      country == "Austria" ~ "Австрия",
      country == "Latvia" ~ "Латвия",
      country == "Lithuania" ~ "Литва",
      country == "Netherlands" ~ "Холандия",
      country == "Norway" ~ "Норвегия",
      country == "Poland" ~ "Полша",
      country == "Portugal" ~ "Португалия",
      country == "Slovakia" ~ "Словакия",
      country == "Slovenia" ~ "Словения",
      country == "Spain" ~ "Испания",
      country == "UK" ~ "Великобритания",
      country == "Belgium" ~ "Белгия",
      country == "Bulgaria" ~ "България",
      country == "Estonia" ~ "Естония",
      country == "Hungary" ~ "Унгария",
      country == "Malta" ~ "Малта",
      country == "Sweden" ~ "Швеция",
      country == "Switzerland" ~ "Швейцария"
    )
  ) |> 
  arrange(-estimate) |> 
  knitr::kable()
  
  
cm  |>
  rowwise() |>
  mutate(rctsum = sum(across(starts_with("rct_")))) |>
  ungroup() |> 
  select(-c(
    2,38:44, 46:58,60:100)) |> 
  collect_model_results(outcome_var = "rctsum") |>
  filter(model_p_value < 0.05 & p.value < 0.05) |>
  select(-term) |>
  mutate_round() |> 
  mutate(
    "95%CI" = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
    p.value = case_when(
      p.value < 0.01 ~ "<.01",
      p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(p.value)
    )) |>
  dplyr::select(1,2,8,5,20) |> 
  knitr::kable()

cm |> 
  select(83:93) |>
  get_summary_stats() |>
  mutate(
    variable = case_when(
      variable == "eucbptr_addressing_fair_access_for_cancer_survivors_to_financial_services" ~ "↑ Достъпа до финансови услуги на преживели заболяване",     
      variable == "eucbptr_assistance_of_researchers_digitaly"   ~ "↑ Персоналната терапия чрез дигитални технологии",                                  
      variable == "eucbptr_creation_of_an_eu_platform_repurposing_of_existing_medicines"    ~ "↑ Използваемост на съществуващи лекарства", 
      variable == "eucbptr_developing_a_roadmap_towards_personalised_prevention" ~ "Пътна карта за персонализирана профилактика",       
      variable == "eucbptr_establishing_a_group_of_new_reference_networks_on_specific_cancer_types" ~ "Нови ЕРМ за РТ",
      variable == "eucbptr_establishing_an_eu_network_of_youth_cancer_survivors" ~ "Европейска мрежа за младежи преживели на рак",                  
      variable == "eucbptr_launching_a_cancer_inequalities_registry"  ~ "Регистър на онкологичните неравенства",                             
      variable == "eucbptr_launching_a_new_project_using_high_performance_computing" ~ "In-silico моделиране на терапевтичния ефект",  
      variable == "eucbptr_seting_up_a_partnership_on_personalised_medicine" ~ "Партньорство за персонализирана медицина",                       
      variable == "eucbptr_strengthening_and_integration_of_telemedicine"  ~ "Телемедицина в ЕРМ и здравните системи",
      variable == "eucbptr_supporting_collaborative_projects_on_cancer_diagnostics"
      ~ "Онкологична диагностика и лечение с помощта на ИИ"
    )
  ) |>
  ggplot(aes(x = mean, y = fct_reorder(variable, mean))) +
  geom_point(size = 3) +
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.2f", mean
    ))),
    hjust = +0.5,
    vjust = -0.5,
    size = 5,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  geom_errorbar(
    aes(xmin = mean - 1.96 * se, xmax = mean + 1.96 * se),
    width = 0.2,
    size = 0.5,
    color = "gray10"
  ) +
  geom_vline(
    xintercept = 3.95,
    lty = 2,
    size = 0.5,
    color = "gray10"
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(1, 5.5),
    breaks = c(seq(1, 5, 1))
  ) +
  guides(
    x = guide_axis(cap = "both"), # Cap both ends
    y = guide_axis(cap = "both") # Cap the upper end
  ) +
  theme(axis.line = element_line(
    linewidth = 0.25,
    color = "black"
  ))+
  labs(x = "", y = "", subtitle = "")

# ggsave(
#   "mean-eurecclinics-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 28,
#   height = 14
# )

cm |> 
  select(83:93) |>
  pivot_longer(cols = 1:11,
              names_to = "variable",
              values_to = "value") |>
  mutate(
    variable = case_when(
      variable == "eucbptr_addressing_fair_access_for_cancer_survivors_to_financial_services" ~ "↑ Достъпа до финансови услуги на преживели заболяване",     
      variable == "eucbptr_assistance_of_researchers_digitaly"   ~ "↑ Персоналната терапия чрез дигитални технологии",                                  
      variable == "eucbptr_creation_of_an_eu_platform_repurposing_of_existing_medicines"    ~ "↑ Използваемост на съществуващи лекарства", 
      variable == "eucbptr_developing_a_roadmap_towards_personalised_prevention" ~ "Пътна карта за персонализирана профилактика",       
      variable == "eucbptr_establishing_a_group_of_new_reference_networks_on_specific_cancer_types" ~ "Нови ЕРМ за РТ",
      variable == "eucbptr_establishing_an_eu_network_of_youth_cancer_survivors" ~ "Европейска мрежа за младежи преживели на рак",                  
      variable == "eucbptr_launching_a_cancer_inequalities_registry"  ~ "Регистър на онкологичните неравенства",                             
      variable == "eucbptr_launching_a_new_project_using_high_performance_computing" ~ "In-silico моделиране на терапевтичния ефект",  
      variable == "eucbptr_seting_up_a_partnership_on_personalised_medicine" ~ "Партньорство за персонализирана медицина",                       
      variable == "eucbptr_strengthening_and_integration_of_telemedicine"  ~ "Телемедицина в ЕРМ и здравните системи",
      variable == "eucbptr_supporting_collaborative_projects_on_cancer_diagnostics"
      ~ "Онкологична диагностика и лечение с помощта на ИИ"
    )
  ) |> 
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(~ variable) |> 
  pairs(adjust = "bonferroni") |>
  tidy() |>
  separate(contrast, into = c("FV", "SV"), sep = " - ", remove = FALSE)  |> 
  mutate(
    FV = gsub("[()]", "", FV),
    SV = gsub("[()]", "", SV)
  ) |> 
  dplyr::select(3,4,6,7,10) |> 
  mutate_round() |>
  mutate(
    lower = estimate - 1.96 * std.error,
    upper = estimate + 1.96 * std.error,
    CI = paste0(round(lower, 2), ", ", round(upper, 2)),
    adj.p.value = case_when(
      adj.p.value < 0.01 ~ "<.01",
      adj.p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(adj.p.value)
    )
  ) |>
  select(1,2,3,8,5) |> 
  knitr::kable()
  

cm |> 
  select(starts_with("eucbptr")) |>
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
    Parameter1 =
      case_when(
        Parameter1 == "eucbptr_addressing_fair_access_for_cancer_survivors_to_financial_services" ~ "↑ Достъпа до финансови услуги на преживели заболяване",     
        Parameter1 == "eucbptr_assistance_of_researchers_digitaly"   ~ "↑ Персоналната терапия чрез дигитални технологии",                                  
        Parameter1 == "eucbptr_creation_of_an_eu_platform_repurposing_of_existing_medicines"    ~ "↑ Използваемост на съществуващи лекарства", 
        Parameter1 == "eucbptr_developing_a_roadmap_towards_personalised_prevention" ~ "Пътна карта за персонализирана профилактика",       
        Parameter1 == "eucbptr_establishing_a_group_of_new_reference_networks_on_specific_cancer_types" ~ "Нови ЕРМ за РТ",
        Parameter1 == "eucbptr_establishing_an_eu_network_of_youth_cancer_survivors" ~ "Европейска мрежа за младежи преживели на рак",                  
        Parameter1 == "eucbptr_launching_a_cancer_inequalities_registry"  ~ "Регистър на онкологичните неравенства",                             
        Parameter1 == "eucbptr_launching_a_new_project_using_high_performance_computing" ~ "In-silico моделиране на терапевтичния ефект",  
        Parameter1 == "eucbptr_seting_up_a_partnership_on_personalised_medicine" ~ "Партньорство за персонализирана медицина",                       
        Parameter1 == "eucbptr_strengthening_and_integration_of_telemedicine"  ~ "Телемедицина в ЕРМ и здравните системи",
        Parameter1 == "eucbptr_supporting_collaborative_projects_on_cancer_diagnostics"
          ~ "Онкологична диагностика и лечение с помощта на ИИ"
      ),
    Parameter2 =
      case_when(
        Parameter2 == "eucbptr_addressing_fair_access_for_cancer_survivors_to_financial_services" ~ "↑ Достъпа до финансови услуги на преживели заболяване",     
        Parameter2 == "eucbptr_assistance_of_researchers_digitaly"   ~ "↑ Персоналната терапия чрез дигитални технологии",                                  
        Parameter2 == "eucbptr_creation_of_an_eu_platform_repurposing_of_existing_medicines"    ~ "↑ Използваемост на съществуващи лекарства", 
        Parameter2 == "eucbptr_developing_a_roadmap_towards_personalised_prevention" ~ "Пътна карта за персонализирана профилактика",       
        Parameter2 == "eucbptr_establishing_a_group_of_new_reference_networks_on_specific_cancer_types" ~ "Нови ЕРМ за РТ",
        Parameter2 == "eucbptr_establishing_an_eu_network_of_youth_cancer_survivors" ~ "Европейска мрежа за младежи преживели на рак",                  
        Parameter2 == "eucbptr_launching_a_cancer_inequalities_registry"  ~ "Регистър на онкологичните неравенства",                             
        Parameter2 == "eucbptr_launching_a_new_project_using_high_performance_computing" ~ "In-silico моделиране на терапевтичния ефект",  
        Parameter2 == "eucbptr_seting_up_a_partnership_on_personalised_medicine" ~ "Партньорство за персонализирана медицина",                       
        Parameter2 == "eucbptr_strengthening_and_integration_of_telemedicine"  ~ "Телемедицина в ЕРМ и здравните системи",
        Parameter2 == "eucbptr_supporting_collaborative_projects_on_cancer_diagnostics"
        ~ "Онкологична диагностика и лечение с помощта на ИИ"
      ),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 45, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "", subtitle = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))+
  theme(
    axis.text = element_text(
      family = "Sofia Sans Condensed", 
      size = 14))  


#  ggsave(
#    "eucbptr-full-criteria-cor-bg.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 28,
#    height = 16
#  )



cm |>
  dplyr::select(starts_with("eucbptr")) |>
  ltm::cronbach.alpha(standardized = T, CI = T)

cm |>
  dplyr::select(starts_with("eucbptr"))|>
  psych::alpha()

cm |>
  dplyr::select(starts_with("eucbptr")) |>
  psych::KMO()

cm |>
  dplyr::select(starts_with("eucbptr")) |>
  psych::cortest.bartlett()

cm |>
  rowwise() |>
  mutate(eucbptrsum = sum(across(starts_with("eucbptr_")))) |>
  ungroup() |>
  dplyr::select(-c(starts_with("eucbptr_"))) |>
  get_summary_stats(eucbptrsum)


cm |>
  rowwise() |>
  mutate(eucbptrsum = sum(across(starts_with("eucbptr_")))) |>
  ungroup() |>
  dplyr::select(-c(starts_with("eucbptr_"))) |> 
  select(-c(
    2, 38:58,60:82))  |>
  to_dummmy() |>
  collect_model_results(outcome_var = "eucbptrsum") |>
  mutate_if(is.numeric, round, 2) |>
  filter(model_p_value < 0.05 & p.value < 0.05) |>
  select(-term) |>
  mutate(
    "95%CI" = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
    p.value = case_when(
      p.value < 0.01 ~ "<.01",
      p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(p.value)
    )) |>
  dplyr::select(1,2,8,5,20) |> 
  knitr::kable()
 


srp <-
  eu |>
  rowwise() |>
  mutate(
    eurecpp = sum(across(c(91:100))),
    ncrsum = sum(across(c(66:77))),
    cppsum = sum(across(c(60:65))),
    ncpsum = sum(across(c(44:51))),
    eucbptrsum = sum(across(starts_with("eucbptr_")))
  ) |>
  ungroup() |>
  select(-c(1:4,14,22, 91:100, 66:77, 60:65, 44:51,125:135,172)) |>
  rename_with(
    ~ gsub(
      "^usability_of_the_available_treatment_guidelines_",
      "gdl_",
      .
    ),
    starts_with("usability_of_the_available_treatment_guidelines_")
  ) |>
  rename_with(
    ~ gsub("^effectiveness_collaboration_", "collab_", .),
    starts_with("effectiveness_collaboration_")
  ) |>
  rename_with(
    ~ gsub("^reimbursement_new_therapies_importance_", "rmbfac_", .),
    starts_with("reimbursement_new_therapies_importance_")
  ) |>
  rename_with(
    ~ gsub("^effectiveness_of_the_clinical_trials_", "rct_", .),
    starts_with("effectiveness_of_the_clinical_trials_")
  ) |> 
  rename_with(
    ~ gsub("^eu_cancer_plan_recommendations_", "eucbptr_", .),
    starts_with("eu_cancer_plan_recommendations_")
  ) |> 
  rename_with(
    ~ gsub("^inovate_therapy_funding_", "itreat_fund_", .),
    starts_with("inovate_therapy_funding_")
  ) |> 
  rename_with(
    ~ gsub("^medico_social_support_services_", "ms_", .),
    starts_with("medico_social_support_services_")
  ) |> 
  rename_with(
    ~ gsub("^palliative_care_", "pal-", .),
    starts_with("palliative_care_")
  ) |> 
  rename_with(
    ~ gsub("^sources_for_social_support_and_palliative_care_", "palfund_", .),
    starts_with("sources_for_social_support_and_palliative_care_")
  ) 



srp |>
  col_n_sum(90) |> 
  pcit() |>
  mutate(
    `pal-included` =
      case_when(
        `pal-included` == "No" ~ "Не се предоставя",
        `pal-included` == "Yes, provided at site" ~ "Предоставя се на място",
        `pal-included` == "Yes, provided by other facilities" ~ "Предоставя от друга институция",
        TRUE ~ `pal-included`
      )
  ) |>
  ggplot(aes(
    x = proportion,
    y = fct_reorder(`pal-included`, proportion),
    fill = `pal-included`
  )) +
  geom_col(width = .5, color = "gray10")  +
  geom_text(
    aes(label = `pal-included`, x = 0),
    family = "Sofia Sans Condensed",
    #fontface = "bold",
    hjust = 0,
    vjust = -2.8,
    size = 7
  ) +
  geom_errorbarh(
    aes(xmin = lower, xmax = upper),
    height = 0.2,
    size = 0.3,
    color = "gray10",
    lty = 1,
    alpha = 0.7
  ) +
  geom_label(
    aes(label = paste0("  ", sprintf(
      "%2.1f", proportion * 100
    ), "%  ")),
    #color = proportion > .05
    #hjust = proportion > .05),
    fill = "white",
    size = 5,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  scale_color_manual(values = c("black", "white"), guide = "none") +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(-0.1, 0.9),
    breaks = c(seq(0, 0.8, 0.2)),
    labels = scales::label_percent()
  ) +
  scale_y_discrete(guide = "none") +
  scale_fill_manual(values = c("gray80", "gray80", "#37B7C3")) +
  theme(
    legend.position = "none",
    axis.title.y = element_blank(),
    axis.text.y = element_blank(),
    axis.ticks.y = element_blank(),
    axis.line.y = element_blank(), 
    axis.line.x = element_line(
      linewidth = 0.25,
      color = "black"),
  ) +
  guides(
    x = guide_axis(cap = "both"))+
  labs(y = "", x = "")


# ggsave(
#   "paliative-included-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 20,
#   height = 15
# )
  
srp |>
  select(`pal-included`) |> 
  table() |> 
  rstatix::chisq_test() |> 
  mutate_round()
 

# srp |> 
#   select(1,3,4,5,6:35,45,59,73:82,90) |>
#   mutate(
#     "pal-included" = case_when(
#       `pal-included` == "No" ~ 0,
#       `pal-included` == "Yes, provided at site" ~ 1,
#       `pal-included` == "Yes, provided by other facilities" ~ 0,
#     )
#   ) |> 
#   rename(
#     "pal_included" = `pal-included`
#   ) |> 
#   to_dummmy() |>
#   tbl_summary(by = pal_included,
#                 type = c# ("evidence_based_treatment_guidelines_for_rare_tumors_available",
#                   "rmbfac_disease_severity_clinical_burden",
#                   "rmbfac_value_for_money_and_budget_impact",
#                   "rmbfac_unmet_need_lack_of_active_treatment_alternatives"# ,
#                   "rmbfac_strength_robustness_quality_of_evidence",
#                   "rct_availability",
#                   "rct_coverage",
#                   "rct_inclusivity",
#                   "rct_affordability",
#                   "rct_contemporary") ~ "continuous",
#                   statistic = all_continuous() ~ "{mean} ({sd})") |> 
#   add_difference() |> 
#   as_flex_table() 

srp |>
  mutate(
    "pal-included" = case_when(
      `pal-included` == "No" ~ 0,
      `pal-included` == "Yes, provided at site" ~ 1,
      `pal-included` == "Yes, provided by other facilities" ~ 0,
    )
  ) |> 
  aov(evidence_based_treatment_guidelines_for_rare_tumors_available ~`pal-included`, data = _) |> 
  emmeans(specs = "pal-included")
  

srp |>
  dplyr::select(90:96) |>
  get_summary_stats() |>
  mutate(
    variable = case_when(
variable == "ms_psychosocial_support" ~ "Психосоциална подкрепа",  
variable == "ms_financial_support" ~ "Финансово подпомагане",            
variable == "ms_occupational_support" ~ "Трудова терапия",         
variable == "ms_additional_medical_support_art_therapy_music_therapy" ~ "Арт терапия и музикотерапия",
variable == "ms_spiritual_and_religious_support" ~ "Духовна и религиозна грижа",                     
variable == "ms_legal_support" ~ "Правна подкрепа",                    
variable == "ms_diet_and_nutrition_support" ~ "Диетологична подкрепа"
    )
  ) |>
  ggplot(aes(x = mean, y = fct_reorder(variable, mean))) +
  geom_point(size = 3) +
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.2f", mean
    ))),
    hjust = +0.5,
    vjust = -0.6,
    size = 5,
    family = "Roboto Condensed",
  ) +
  geom_errorbar(
    aes(xmin = mean - 1.96 * se, xmax = mean + 1.96 * se),
    width = 0.2,
    size = 0.5,
    color = "gray10"
  ) +
  geom_vline(
    xintercept = 3.70,
    lty = 2,
    size = 0.5,
    color = "gray10"
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(1, 5.5),
    breaks = c(seq(1, 5, 1))
  ) +
  guides(
    x = guide_axis(cap = "both"), # Cap both ends
    y = guide_axis(cap = "both") # Cap the upper end
  ) +
  theme(axis.line = element_line(
    linewidth = 0.25,
    color = "black"
  ))+
  labs(x = "", y = "", subtitle = "")

#  ggsave("medicosocial-mean-bg.png",
#         device = "png",
#         bg = "white",
#         units = "mm",
#         width = 200,
#         height = 130,
#         dpi = 1000)
#  

srp |>
  dplyr::select(91:97) |>
  pivot_longer(cols = 1:7,
              names_to = "variable",
              values_to = "value") |>
    mutate(
      variable = case_when(
        variable == "ms_psychosocial_support" ~ "Психосоциална подкрепа",  
        variable == "ms_financial_support" ~ "Финансово подпомагане",            
        variable == "ms_occupational_support" ~ "Трудова терапия",         
        variable == "ms_additional_medical_support_art_therapy_music_therapy" ~ "Арт терапия и музикотерапия",
        variable == "ms_spiritual_and_religious_support" ~ "Духовна и религиозна грижа",                     
        variable == "ms_legal_support" ~ "Правна подкрепа",                    
        variable == "ms_diet_and_nutrition_support" ~ "Диетологична подкрепа"
      )
    ) |> 
  aov(value ~ variable, data = _) |>
  emmeans::emmeans(~ variable) |>
  pairs(adjust = "bonferroni") |>
  tidy() |>
  separate(contrast, into = c("FV", "SV"), sep = " - ", remove = FALSE)  |>
  mutate(
    FV = gsub("[()]", "", FV),
    SV = gsub("[()]", "", SV)
  ) |>
  dplyr::select(3,4,6,7,10) |>
  mutate_round() |>
  mutate(
    lower = estimate - 1.96 * std.error,
    upper = estimate + 1.96 * std.error,
    CI = paste0(round(lower, 2), ", ", round(upper, 2)),
    adj.p.value = case_when(
      adj.p.value < 0.01 ~ "<.01",
      adj.p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(adj.p.value)
    )
  ) |>
  select(1,2,3,8,5) |>
  knitr::kable()
  
srp |>
dplyr::select(91:97) |>
  pivot_longer(cols = 1:7,
               names_to = "variable",
               values_to = "value") |>
  mutate(
    variable = case_when(
      variable == "ms_psychosocial_support" ~ "Психосоциална подкрепа",  
      variable == "ms_financial_support" ~ "Финансово подпомагане",            
      variable == "ms_occupational_support" ~ "Трудова терапия",         
      variable == "ms_additional_medical_support_art_therapy_music_therapy" ~ "Арт терапия и музикотерапия",
      variable == "ms_spiritual_and_religious_support" ~ "Духовна и религиозна грижа",                     
      variable == "ms_legal_support" ~ "Правна подкрепа",                    
      variable == "ms_diet_and_nutrition_support" ~ "Диетологична подкрепа"
    )
  ) |> 
  mutate(
  ftc = case_when(
    value == "1" ~ "Disagree",
    value == "2" ~ "Disagree",
    value == "3" ~ "Neutral",
    value == "4" ~ "Agree",
    value == "5" ~ "Agree"
  )) |>
  count(variable, ftc) |>
  pivot_wider(names_from = ftc, values_from = n) |>
  mutate(
    
  ) |>
  mutate(
    total = Agree + Disagree + Neutral,
    Agree = (Agree + 0.5*Neutral) / total 
  ) |>
  select(variable, Agree) |>
  mutate(
    Agree = Agree/0.5
  ) |>
  
  
  
srp_model <- 
  srp |>
  select(-country) |>
  pivot_longer(cols = 90:96,
               names_to = "variable",
               values_to = "value") |>
  rename(pal_included = `pal-included`) |>
  mutate(
    variable = case_when(
      variable == "ms_psychosocial_support" ~ "Психосоциална подкрепа",  
      variable == "ms_financial_support" ~ "Финансово подпомагане",            
      variable == "ms_occupational_support" ~ "Трудова терапия",         
      variable == "ms_additional_medical_support_art_therapy_music_therapy" ~ "Арт терапия и музикотерапия",
      variable == "ms_spiritual_and_religious_support" ~ "Духовна и религиозна грижа",                     
      variable == "ms_legal_support" ~ "Правна подкрепа",                    
      variable == "ms_diet_and_nutrition_support" ~ "Диетологична подкрепа"
    )
  ) |> 
  select(-c(90:110)) |> 
  group_by(variable) |>
  nest() |>
  mutate(
    models = map(data,~.x |>
                   to_dummmy() |>
                   collect_model_results(outcome_var = "value")
    )
  )

srp_model |> 
  unnest(models) |>
  select(-data) |> 
  filter(model_p_value < 0.05 & p.value < 0.05) |>
  select(-term) |>
  mutate_round() |>
  mutate(
    "95%CI" = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
    p.value = case_when(
      p.value < 0.01 ~ "<.01",
      p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(p.value)
    )) |> 
  dplyr::select(1,2,3,9,6,21) |>
  flextable::flextable() 

srp |>
  select(area_of_rare_cancers_haematological_rare_cancers, starts_with("ms_")) |>
  pivot_longer(
    cols = 2:8,
    names_to = "variable",
    values_to = "value"
  ) |>
  group_by(variable) |>
  nest() |>
  mutate(
    models = map(data, ~.x |>
                   aov(value ~ area_of_rare_cancers_haematological_rare_cancers, data = _) |>
                   emmeans(specs = "area_of_rare_cancers_haematological_rare_cancers") |> 
                   pairs(adjust = "bonferroni", reverse = TRUE) |>
                   tidy())) |> 
  unnest(models) |>
  select(-data) |>
  mutate(
    variable = case_when(
      variable == "ms_psychosocial_support" ~ "Психосоциална подкрепа",  
      variable == "ms_financial_support" ~ "Финансово подпомагане",            
      variable == "ms_occupational_support" ~ "Трудова терапия",         
      variable == "ms_additional_medical_support_art_therapy_music_therapy" ~ "Арт терапия и музикотерапия",
      variable == "ms_spiritual_and_religious_support" ~ "Духовна и религиозна грижа",                     
      variable == "ms_legal_support" ~ "Правна подкрепа",                    
      variable == "ms_diet_and_nutrition_support" ~ "Диетологична подкрепа"
    )
  ) |> 
  mutate(
    lci = estimate - 1.96 * std.error,
    uci = estimate + 1.96 * std.error,
    CI = paste0(round(lci, 2), ", ", round(uci, 2)),
    p.value = case_when(
      p.value < 0.001 ~ "***",
      p.value < 0.01 ~ "**",
      p.value < 0.05 ~ "*",
      TRUE ~ ""
    )) |>
  ggplot(aes(
    x = estimate,
    y = fct_reorder(variable, estimate)
  )) +
  geom_point(size = 3) +
  geom_errorbar(
    aes(
      xmin = lci,
      xmax = uci
    ),
    width = 0.2,
    alpha = 0.7,
    size = 0.5
  ) +
  geom_vline(
    xintercept = 0,
    lty = 2,
    size = 0.5,
    color = "gray10"
  ) +
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.2f", estimate), p.value)),
    hjust = +0.5,
    vjust = -0.52,
    size = 6,
    family = "Sofia Sans Condensed",
  ) +
  scale_x_continuous(
    breaks = c(seq(-2, 2, 1)),
    limits = c(-2, 2.2),
    expand = c(0, 0)
  )+
  guides(
    x = guide_axis(cap = "both"), # Cap both ends
    y = guide_axis(cap = "both") # Cap the upper end
  ) +
  theme(axis.line = element_line(),
        axis.title.x = element_text(size = 16))+
  labs(x = "Δ (95% CI) \nЕкспертиза (хематологични РТ) -  Експертиза (друга)",y = "")

#  ggsave(
#    "hem-social-med-bg.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 20,
#    height = 12
#  )



  

srp |>
rename_with( ~ gsub("^pal-", "pal_", .), starts_with("pal-")) |>
select(98:111) |>
pivot_longer(cols = 1:14,
              names_to = "variable",
              values_to = "value") |>
separate(
   variable,
   sep = "_",
   into = c("pal", "age", "criteria"),
   extra = "merge",
   remove = FALSE
 ) |>
select(-pal) |>
group_by(age, criteria) |>
get_summary_stats() |>
mutate(
   criteria = case_when(
     criteria == "access"  ~ "Достъпност",
     criteria == "availability" ~ "Наличност",
     criteria == "grieving_support" ~ "Подкрепа в траур",
     criteria == "patient_centeredness" ~ "Персонализираност",
     criteria == "quality_of_care" ~ "Качество",
     criteria == "symptoms_management" ~ "Управление на симптомите",
     criteria == "timing" ~ "Навременност"
   )
 ) |>
ggplot(aes(
   x = mean,
   y = fct_reorder(criteria, mean),
   color = age
 )) +
geom_point(size = 3, position =  position_dodge(width = 0.8)) +
geom_text(
   aes(label = paste0("  ", sprintf("%2.2f", mean))),
   hjust = +0.5,
   vjust = -0.6,
   position = position_dodge(width = 0.8),
   size = 5,
   show.legend = FALSE,
   family = "Roboto Condensed",
 ) +
geom_errorbar(
   aes(xmin = mean - 1.96 * se, xmax = mean + 1.96 * se),
   width = 0.2,
   size = 0.5,
   position =  position_dodge(width = 0.8)
 ) +
geom_vline(
    xintercept = 3.75,
    lty = 2,
    size = 0.25,
    color = "#C80036"
  ) +
geom_vline(
  xintercept = 3.24,
  lty = 2,
  size = 0.25,
  color = "#03346E"
) +
scale_x_continuous(
   expand = c(0, 0),
   limits = c(1, 5.5),
   breaks = c(seq(1, 5, 1))
 ) +
scale_color_manual(
    values = c("#C80036", "#03346E"),  # Adjust colors as needed
    labels = c("Възрастни", "Деца"),  # Custom legend labels
    name = ""  # Custom legend title
  )+
guides(x = guide_axis(cap = "both"),
       y = guide_axis(cap = "both"))+
theme(
  legend.text = element_text(size = 16, family = "Sofia Sans Condensed"),
  # Align legend with the plot
  legend.justification = c(1, 0),
  legend.position = c(0.25, 0.1),
  legend.key.size = unit(0.5, "lines"), 
  axis.line = element_line(linewidth = 0.25, color = "black")
) +
  labs(x = "", y = "", subtitle = "")

#  ggsave("paliative-mean-bg.png",
#         device = "png",
#         bg = "white",
#         units = "mm",
#         width = 240,
#         height = 140,
#         dpi = 1000)
#


srp |>
  rename_with( ~ gsub("^pal-", "pal_", .), starts_with("pal-")) |>
  select(98:111) |>
  pivot_longer(cols = 1:14,
               names_to = "variable",
               values_to = "value") |>
  separate(
    variable,
    sep = "_",
    into = c("pal", "age", "criteria"),
    extra = "merge",
    remove = FALSE
  ) |>
  select(-c(pal, variable)) |>
  group_by(age, criteria) |>
  mutate(
    criteria = case_when(
      criteria == "access"  ~ "Достъпност",
      criteria == "availability" ~ "Наличност",
      criteria == "grieving_support" ~ "Подкрепа в траур",
      criteria == "patient_centeredness" ~ "Персонализираност",
      criteria == "quality_of_care" ~ "Качество",
      criteria == "symptoms_management" ~ "Управление на симптомите",
      criteria == "timing" ~ "Навременност"
    )
  ) |>
  group_by(criteria) |>
  nest() |>
  mutate(
    anovite = map(data, ~.x |>
                    aov(value ~ age, data = _) |>
                    emmeans(specs = "age") |>
                    pairs(adjust = "bonferroni", reverse = TRUE) |>
                    tidy())) |>
  unnest(anovite) |>
  mutate(
    p.value = case_when(
      p.value < 0.001 ~ "***",
      p.value < 0.01 ~ "**",
      p.value < 0.05 ~ "*",
      TRUE ~ ""
    )) |> 
  ggplot(aes(
    x = estimate,
    y = fct_reorder(criteria, estimate),
  )) +
  geom_point(size = 3) +
  geom_text(
    aes(label = paste0("  ", sprintf("%2.2f", estimate), 
                       p.value)),
    hjust = +0.5,
    vjust = -0.6,
    size = 5,
    family = "Roboto Condensed",
  ) +
  geom_errorbar(
    aes(xmin = estimate - 1.96 * std.error, 
        xmax = estimate + 1.96 * std.error),
    width = 0.2,
    size = 0.5
  ) +
  geom_vline(
    xintercept = 0,
    lty = 2,
    size = 0.5,
    color = "gray10"
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(-2.25,2.25),
    breaks = c(seq(-2, 2, 1))
  ) +
  guides(x = guide_axis(cap = "both"),
         y = guide_axis(cap = "both"))+
  theme(
    axis.line = element_line(linewidth = 0.25, color = "black")
  ) +
  labs(x = "Δ (95% CI) Деца - Възрастни", 
       y = "", subtitle = "")

#  ggsave(
#    "paliative-age-bg.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 20,
#    height = 12
#  )


srp |>
  rename_with( ~ gsub("^pal-", "pal_", .), starts_with("pal-")) |>
  select(98:111) |>
  pivot_longer(cols = 1:14,
               names_to = "variable",
               values_to = "value") |>
  separate(
    variable,
    sep = "_",
    into = c("pal", "age", "criteria"),
    extra = "merge",
    remove = FALSE
  ) |>
  select(-c(pal, variable)) |>
  filter(age == "adl") |>
  mutate(
    criteria = case_when(
      criteria == "access"  ~ "Достъпност",
      criteria == "availability" ~ "Наличност",
      criteria == "grieving_support" ~ "Подкрепа в траур",
      criteria == "patient_centeredness" ~ "Персонализираност",
      criteria == "quality_of_care" ~ "Качество",
      criteria == "symptoms_management" ~ "Управление на симптомите",
      criteria == "timing" ~ "Навременност"
    )
  ) |>
  aov(value~ criteria, data = _) |> 
  emmeans(specs = "criteria") |>
  pairs(adjust = "bonferroni") |>
  tidy() |>
  separate(contrast, into = c("FV", "SV"), sep = " - ", remove = FALSE)  |>
  mutate(
    FV = gsub("[()]", "", FV),
    SV = gsub("[()]", "", SV)
  ) |>
  dplyr::select(3,4,6,7,10) |>
  mutate_round() |>
  mutate(
    lower = estimate - 1.96 * std.error,
    upper = estimate + 1.96 * std.error,
    CI = paste0(round(lower, 2), ", ", round(upper, 2)),
    adj.p.value = case_when(
      adj.p.value < 0.01 ~ "<.01",
      adj.p.value > 0.90 ~ "> .90",
      TRUE ~ as.character(adj.p.value)
    )
  ) |>
  select(1,2,3,8,5) |>
  knitr::kable()


cor_adl_srp  <- 
  srp |> 
  rename_with( ~ gsub("^pal-", "pal_", .), starts_with("pal-")) |>
  select(98,100,102,104,106,108,110) |>
  correlation(redundant = TRUE) |>
  tibble() |>
  separate(
    Parameter1,
    into = c("del", "Parameter1"),
    sep = "adl_",
    remove = T,
    extra = "merge"
  ) |>
  select(-del) |>
  separate(
    Parameter2,
    into = c("del", "Parameter2"),
    sep = "adl_",
    remove = T,
    extra = "merge"
  ) |> 
  select(-del) |>
  mutate(
    Parameter1 = case_when(
      Parameter1 == "access"  ~ "Достъпност",
      Parameter1 == "availability" ~ "Наличност",
      Parameter1 == "grieving_support" ~ "Подкрепа в траур",
      Parameter1 == "patient_centeredness" ~ "Персонализираност",
      Parameter1 == "quality_of_care" ~ "Качество",
      Parameter1 == "symptoms_management" ~ "Управление на симптомите",
      Parameter1 == "timing" ~ "Навременност"
    ),
    Parameter2 = case_when(
      Parameter2 == "access"  ~ "Достъпност",
      Parameter2 == "availability" ~ "Наличност",
      Parameter2 == "grieving_support" ~ "Подкрепа в траур",
      Parameter2 == "patient_centeredness" ~ "Персонализираност",
      Parameter2 == "quality_of_care" ~ "Качество",
      Parameter2 == "symptoms_management" ~ "Управление на симптомите",
      Parameter2 == "timing" ~ "Навременност"),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 45, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "", subtitle = "А. Възрастни") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))


cor_cld_srp  <- 
  srp |> 
  rename_with( ~ gsub("^pal-", "pal_", .), starts_with("pal-")) |>
  select(99,101,103,105,107,109,111) |>
  correlation(redundant = TRUE) |>
  tibble() |>
  separate(
    Parameter1,
    into = c("del", "Parameter1"),
    sep = "cld_",
    remove = T,
    extra = "merge"
  ) |>
  select(-del) |>
  separate(
    Parameter2,
    into = c("del", "Parameter2"),
    sep = "cld_",
    remove = T,
    extra = "merge"
  ) |> 
  select(-del) |>
  mutate(
    Parameter1 = case_when(
      Parameter1 == "access"  ~ "Достъпност",
      Parameter1 == "availability" ~ "Наличност",
      Parameter1 == "grieving_support" ~ "Подкрепа в траур",
      Parameter1 == "patient_centeredness" ~ "Персонализираност",
      Parameter1 == "quality_of_care" ~ "Качество",
      Parameter1 == "symptoms_management" ~ "Управление на симптомите",
      Parameter1 == "timing" ~ "Навременност"
    ),
    Parameter2 = case_when(
      Parameter2 == "access"  ~ "Достъпност",
      Parameter2 == "availability" ~ "Наличност",
      Parameter2 == "grieving_support" ~ "Подкрепа в траур",
      Parameter2 == "patient_centeredness" ~ "Персонализираност",
      Parameter2 == "quality_of_care" ~ "Качество",
      Parameter2 == "symptoms_management" ~ "Управление на симптомите",
      Parameter2 == "timing" ~ "Навременност"),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")
  ) |>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 45, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "", y = "", subtitle = "В. Деца") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))


cor_adl_srp/ cor_cld_srp

# ggsave(
#   "paliative-full-criteria-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 25,
#   height = 28
# )


srp |>
  select(98:111) |> 
  correlation(
    select = c(
      "pal-adl_availability",
      "pal-adl_access",
      "pal-adl_quality_of_care",
      "pal-adl_timing",
      "pal-adl_patient_centeredness",
      "pal-adl_symptoms_management",  
      "pal-adl_grieving_support"),
    select2 = c(
      "pal-cld_availability",
      "pal-cld_access",
      "pal-cld_quality_of_care",
      "pal-cld_timing",
      "pal-cld_patient_centeredness", 
      "pal-cld_symptoms_management", 
      "pal-cld_grieving_support"   
    )) |>
  tibble() |>
  rename(
    adults = "Parameter1",
    children = "Parameter2"
  ) |> 
  separate(
    adults,
    into = c("del", "adults"),
    sep = "pal-adl_",
    remove = T,
    extra = "merge"
  ) |>
  select(-del) |>
  separate(
    children,
    into = c("del", "children"),
    sep = "pal-cld_",
    remove = T,
    extra = "merge"
  ) |>
  select(-del) |>
  mutate(children = case_when(
        children == "access"  ~ "Достъпност",
        children == "availability" ~ "Наличност",
        children == "grieving_support" ~ "Подкрепа в траур",
        children == "patient_centeredness" ~ "Персонализираност",
        children == "quality_of_care" ~ "Качество",
        children == "symptoms_management" ~ "Управление на симптомите",
        children == "timing" ~ "Навременност"
      ),
      adults = case_when(
        adults  == "access"  ~ "Достъпност",
        adults  == "availability" ~ "Наличност",
        adults  == "grieving_support" ~ "Подкрепа в траур",
        adults  == "patient_centeredness" ~ "Персонализираност",
        adults  == "quality_of_care" ~ "Качество",
        adults  == "symptoms_management" ~ "Управление на симптомите",
        adults  == "timing" ~ "Навременност"),
      p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ "")) |>
  ggplot(aes(adults, children, fill = r)) +
  geom_tile(color = "white") +
  scale_fill_gradient2(
    low = "#4158A6",
    high = "#FF8343",
    mid = "white",
    midpoint = 0,
    limit = c(-1, 1),
    space = "Lab",
    name = ""
  ) +
  geom_text(aes(label = paste0(round(r, 2), 
                               p_astr)), 
            color = "black", 
            family = "Sofia Sans Condensed",
            size = 5) +
  theme(axis.text.x = element_text(angle = 40, 
                                   vjust = 1, 
                                   hjust = 1)) +
  geom_rangeframe()+
  theme(
    # legend.justification = c(1, 0),
    # legend.position = c(0.6, 0.7),
    legend.direction = "vertical")+
  labs(x = "Възрастни", y = "Деца", subtitle = "") +
  guides(fill = guide_colorbar(barwidth = 1.5, 
                               barheight = 12,
                               title.hjust = 0.5))+
  theme(axis.text = element_text(
    family = "Sofia Sans Condensed", 
    size = 20))


# ggsave(
#   "paliative-cross-cor-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 28,
#   height = 16
# )


paliative_models <- 
  srp |>
  rename_with( ~ gsub("^pal-", "pal_", .), starts_with("pal-")) |>
  pivot_longer(cols = 98:111,
               names_to = "variable",
               values_to = "value") |>
  separate(
    variable,
    sep = "_",
    into = c("pal", "age", "criteria"),
    extra = "merge",
    remove = FALSE
  ) |>
  select(-c(pal, variable)) |>
  mutate(
    criteria = case_when(
      criteria == "access"  ~ "Достъпност",
      criteria == "availability" ~ "Наличност",
      criteria == "grieving_support" ~ "Подкрепа в траур",
      criteria == "patient_centeredness" ~ "Персонализираност",
      criteria == "quality_of_care" ~ "Качество",
      criteria == "symptoms_management" ~ "Управление на симптомите",
      criteria == "timing" ~ "Навременност"
    )
  ) |> 
  mutate(
    criteria = paste0(criteria, " (", age, ")")
  ) |>
  select(-c(1,59:88,97:103,111)) |> 
  group_by(criteria) |>
  nest() |>
  mutate(
    models = map(data, ~.x |>
                   to_dummmy() |>
                   collect_model_results(outcome_var = "value")
    ))
  
  

srp |>
  rename_with( ~ gsub("^pal-", "pal_", .), starts_with("pal-")) |>
  select(98:111,hcepc_hight) |>
  pivot_longer(cols = 1:14,
               names_to = "variable",
               values_to = "value") |>
  separate(
    variable,
    sep = "_",
    into = c("pal", "age", "criteria"),
    extra = "merge",
    remove = FALSE
  ) |>
  select(-c(pal, variable)) |>
  mutate(
    criteria = case_when(
      criteria == "access"  ~ "Достъпност",
      criteria == "availability" ~ "Наличност",
      criteria == "grieving_support" ~ "Подкрепа в траур",
      criteria == "patient_centeredness" ~ "Персонализираност",
      criteria == "quality_of_care" ~ "Качество",
      criteria == "symptoms_management" ~ "Управление на симптомите",
      criteria == "timing" ~ "Навременност"
    )
  ) |>
  group_by(age, criteria) |>
  nest() |>
  mutate(
    anovite = map(data, ~.x |>
                    aov(value ~ hcepc_hight , data = _) |>
                    emmeans(specs = "hcepc_hight") |>
                    pairs(adjust = "bonferroni", reverse = TRUE) |>
                    tidy())) |>
  unnest(anovite) |>
  select(-data) |>
  mutate(
    pstar = case_when(
      p.value < 0.001 ~ "***",
      p.value < 0.01 ~ "**",
      p.value < 0.05 ~ "*",
      TRUE ~ ""
    )) |>
  ggplot(aes(
    x = estimate,
    y = fct_reorder(criteria, estimate),
    color = age
  )) +
  geom_point(size = 3, position =  position_dodge(width = 0.8)) +
  geom_text(
    aes(label = paste0("  ", sprintf("%2.2f", estimate), pstar)),
    hjust = +0.5,
    vjust = -0.6,
    position = position_dodge(width = 0.8),
    size = 5,
    show.legend = FALSE,
    family = "Roboto Condensed",
  ) +
  geom_errorbar(
    aes(xmin = estimate - 1.96 * std.error, 
        xmax = estimate + 1.96 * std.error),
    width = 0.2,
    size = 0.5,
    position =  position_dodge(width = 0.8)
  ) +
  geom_vline(
    xintercept = 0,
    lty = 2,
    size = 0.5,
    color = "gray10"
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(-2.25,2.25),
    breaks = c(seq(-2, 2, 1))
  ) +
  guides(x = guide_axis(cap = "both"),
         y = guide_axis(cap = "both"))+
  scale_color_manual(
    values = c("#C80036", "#03346E"),  # Adjust colors as needed
    labels = c("Възрастни", "Деца"),  # Custom legend labels
    name = ""  # Custom legend title
  )+
  theme(
    legend.text = element_text(size = 16, family = "Sofia Sans Condensed"),
    # Align legend with the plot
    legend.justification = c(1, 0),
    legend.position = c(0.9, 0.1),
    legend.key.size = unit(0.5, "lines"), 
    axis.line = element_line(linewidth = 0.25, color = "black")
  ) +
  labs(x = "Δ (95% CI) Виоки - Ниски ПРЗГН", y = "", subtitle = "")


# ggsave(
#   "paliative-by-hcec-bg.png",
#   bg = "white",
#   units = "cm",
#   dpi = 1000,
#   width = 20,
#   height = 15)


 
 srp |>
   dplyr::select(112:118) |>
   get_summary_stats() |> 
   select(variable, mean, ci) |> 
   mutate(
     LCI = mean-ci, 
     UCI = mean+ci,
   ) |> 
   mutate_round() |> 
   select(-ci) |> 
   arrange(-mean) 

 
 
 srp |>
   dplyr::select(112:118) |> 
   pivot_longer(cols = 1:7,
                names_to = "variable",
                values_to = "value") |>
   mutate(variable = 
            case_when(
              variable == "palfund_other_eu_financing_project_lines" ~ "ЕС",               
              variable == "palfund_other_industry" ~ "Индустрия",                                 
              variable == "palfund_other_non_profit_institutions_serving_households" ~ "НПО",
              variable == "palfund_private_household_out_of_pocket_expenditure" ~ "Лични разходи",
              variable == "palfund_private_voluntary_health_insurance_funding" ~ "ДОФ",     
              variable == "palfund_public_goverment_funding" ~ "Държавно финансиране",            
              variable == "palfund_public_health_insurance_funding" ~ "ЗОФ"
            )) |> 
   aov(value ~ variable, data = _) |>
   emmeans(specs = "variable") |>
   pairs(adjust = "bonferroni") |>
   tidy() |>
   separate(contrast, into = c("FV", "SV"), sep = " - ", remove = FALSE)  |>
   mutate(
     FV = gsub("[()]", "", FV),
     SV = gsub("[()]", "", SV)
   ) |>
   mutate_round() |>
   mutate(
     lower = estimate - 1.96 * std.error,
     upper = estimate + 1.96 * std.error,
     CI = paste0(round(lower, 2), ", ", round(upper, 2)),
     adj.p.value = case_when(
       adj.p.value < 0.01 ~ "<.01",
       adj.p.value > 0.90 ~ "> .90",
       TRUE ~ as.character(adj.p.value)
     )
   ) |>
   select(3,4,6,10) |> 
   knitr::kable()

 
 pal_fund_models <- 
   srp |>
   pivot_longer(cols = 112:118,
                names_to = "variable",
                values_to = "value") |>
   mutate(variable = 
            case_when(
              variable == "palfund_other_eu_financing_project_lines" ~ "ЕС",               
              variable == "palfund_other_industry" ~ "Индустрия",                                 
              variable == "palfund_other_non_profit_institutions_serving_households" ~ "НПО",
              variable == "palfund_private_household_out_of_pocket_expenditure" ~ "Лични разходи",
              variable == "palfund_private_voluntary_health_insurance_funding" ~ "ДОФ",     
              variable == "palfund_public_goverment_funding" ~ "Държавно финансиране",            
              variable == "palfund_public_health_insurance_funding" ~ "ЗОФ"
            )) |> 
   group_by(variable) |>
   nest() |>
   mutate(
     models = map(data, ~.x |>
                    to_dummmy() |>
                    collect_model_results(outcome_var = "value")
     )
   )

 pal_fund_models |>
   unnest(models) |>
   select(-data) |>
   filter(model_p_value < 0.05 & p.value < 0.05) |>
   select(-term) |>
   mutate_round() |>
   mutate(
     "95%CI" = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
     p.value = case_when(
       p.value < 0.01 ~ "<.001",
       p.value > 0.90 ~ "> .90",
       TRUE ~ as.character(p.value)), 
     ) |> 
   dplyr::select(1,2,3,9,6,21) |> 
   flextable::flextable() 
 

 f1 <- 
 srp |>
   dplyr::select(112:118) |>
   pivot_longer(cols = 1:7,
                names_to = "variable",
                values_to = "value") |>
   mutate(
     fct_var = case_when(
       value == 1 ~ "no",
       value == 2 ~ "no",
       value == 3 ~ "both",
       value == 4 ~ "yes",
       value == 5 ~ "yes"
     )
   ) |>
   count(variable, fct_var) |>
   group_by(variable) |>
   pivot_wider(names_from = fct_var, values_from = n) |>
   mutate(
     agreement = (yes + 0.5 * both) / 92,
     disagreement = (no + 0.5 * both) / 92,
     adr = agreement / disagreement,
     adr1 = ifelse(adr > 1, TRUE, FALSE)
   ) |>
   dplyr::select(variable, agreement, disagreement, adr, adr1) |>
   ggplot(aes(
     x = agreement,
     y = fct_reorder(variable, agreement),
     fill = adr1
   )) +
   geom_col(color = "gray10", alpha = 0.7) +
   geom_vline(
     xintercept = 0.5,
     lty = 2,
     size = 0.5,
     color = "#013440"
   ) +
   geom_text(
     aes(label = paste0("  ", sprintf(
       "%2.1f", agreement * 100
     ), "%  ")),
     #color = agreement > .05
     #hjust = agreement > .05),
     hjust = "right",
     size = 5,
     fontface = "bold",
     family = "Roboto Condensed",
   ) +
   scale_fill_manual(values = generate_palette("#37B7C3", 
                                               modification = "go_both_ways", 
                                               n_colours = 2))+
   scale_x_continuous(
     expand = c(0, 0),
     limits = c(-0.05, 1.1),
     breaks = c(seq(0, 1, 0.2)),
     labels = scales::label_percent()
   ) +
   scale_y_discrete(
     labels = c(
       "palfund_other_eu_financing_project_lines" = "ЕС",               
       "palfund_other_industry" = "Индустрия",                                 
       "palfund_other_non_profit_institutions_serving_households" = "НПО",
       "palfund_private_household_out_of_pocket_expenditure" = "Лични разходи",
       "palfund_private_voluntary_health_insurance_funding" = "ДОФ",     
       "palfund_public_goverment_funding" = "Държавно финансиране",            
       "palfund_public_health_insurance_funding" = "ЗОФ"     
     )
   ) +
   guides(
     x = guide_axis(cap = "both"),
     y = guide_axis(cap = "both")
   )+
   theme(legend.position = "none", 
         axis.line = element_line(linewidth = 0.30, color = "black"))+
   labs(y = "", x = "%Одобрение")
 

 f2 <- 
   srp |>
   dplyr::select(112:118) |>
   pivot_longer(cols = 1:7,
                names_to = "variable",
                values_to = "value") |>
   aov(value ~ variable, data = _) |>
   emmeans::emmeans(specs = "variable") |>
   tidy() |>
   ggplot(aes(x = estimate, y = fct_reorder(variable, estimate))) +
   geom_point(aes(color = variable), size = 3) +
   geom_text(
     aes(label = paste0("  ", sprintf(
       "%2.2f", estimate
     ))),
     hjust = +0.5,
     vjust = -0.5,
     size = 5,
     fontface = "bold",
     family = "Roboto Condensed",
   ) +
   geom_errorbar(
     aes(
       xmin = estimate - 1.96 * std.error,
       xmax = estimate + 1.96 * std.error,
       colour = variable
     ),
     width = 0.2,
     alpha = 0.7,
     size = 0.5,
   ) +
   geom_vline(
     xintercept = 2.77,
     lty = 2,
     size = 0.5,
     color = "gray10"
   ) +
   scale_y_discrete(
     labels = c(
       
       "palfund_other_eu_financing_project_lines" = "Програми и фондове на ЕС",         
       "palfund_other_industry" = "Индустрия",                            
       "palfund_other_non_profit_institutions_serving_households" = "НПО",
       "palfund_private_household_out_of_pocket_expenditure" =  "Лични разходи",
       "palfund_private_voluntary_health_insurance_funding" = "Доброволни ЗОФ",   
       "palfund_public_goverment_funding" = "Държавно финансиране",       
       "palfund_public_health_insurance_funding" = "Задължителни ЗОФ"
     )
   ) +
   scale_x_continuous(
     expand = c(0, 0),
     limits = c(1, 5.5),
     breaks = c(seq(1, 5, 1))
   ) +
   theme(legend.position = "none") +
   scale_color_manual(values = c(
     "#03346E",
     "#03346E",
     "#03346E",
     "#973131",
     "#973131",
     "#059212",
     "#059212"
   )) +
   guides(
     x = guide_axis(cap = "both"),
     y = guide_axis(cap = "both")
   ) +
   labs(x = "", y = "", subtitle = "")+
   theme(
     axis.line.y = element_blank(),
     axis.text.y =  element_blank(),
     axis.ticks.y = element_blank(),
     axis.line = element_line(linewidth = 0.25, color = "black"))
 
 f1+f2
 
#  ggsave(
#    "paliative-agr-bg.png",
#    bg = "white",
#    units = "cm",
#    dpi = 1000,
#    width = 30,
#    height = 12
#  ) 
 
 

 
  