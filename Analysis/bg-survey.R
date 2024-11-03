
######---Load packages---######
library(tidyverse)
library(ggdist)
library(survival)
library(ranger)
library(ggfortify)
library(modelsummary)
library(MKinfer)
library(rstatix)
library(finalfit)
library(tinytable)
library(monochromeR)
library(ggstats)
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
library(gt)
library(epiR)
library(readxl)
library(scales)
library(marginaleffects)
library(ggthemes)
library(emmeans)
library(janitor)
library(easystats)
# options(brms.backend = "cmdstanr")


######---Define my own functions---######


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

collect_ordinal_logistic_results <- function(df, outcome_var) {
  predictors <- setdiff(names(df), outcome_var)
  
  results <- lapply(predictors, function(predictor) {
    # Clean the predictor name by replacing "-" with "_"
    clean_predictor <- gsub("-", "_", predictor)
    
    # Clean the column name in the dataframe
    colnames(df)[colnames(df) == predictor] <- clean_predictor
    
    # Create the formula with the cleaned predictor name
    formula <- as.formula(paste(outcome_var, "~", clean_predictor))
    
    # Fit the ordinal regression model
    model <- ordinal::clm(formula, data = df)
    
    # Use broom::tidy() to extract the OR, confidence intervals, and p-values
    coef_details <- broom::tidy(model, exp = TRUE, conf.int = TRUE) %>%
      dplyr::mutate(predictor = clean_predictor) %>%
      dplyr::select(predictor, term, OR = estimate, conf.low, conf.high, p.value)
    
    return(coef_details)
  })
  
  # Combine results into a single tibble
  results_df <- dplyr::bind_rows(results)
  return(results_df)
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
    mutate(across(where(is.numeric), ~ janitor::round_half_up(., digits)))
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

sample <- 
  tibble::tribble(
                     ~side, ~general, ~sample,
                "Академия",       10,       9,
     "Законодателна власт",       37,      17,
            "Изпълнителна",       95,      45,
               "Индустрия",       41,      16,
        "Научни дружества",       24,       7,
  "Пациентски организации",       54,       9,
    "Съсловни организации",       23,       7
  )


gp <- 
  sample |>
  select(side,general) |> 
  mutate(sum = sum(general), 
         prop_gp = 100*(general / sum)) |>
  select(-sum) 
  
smp <- 
  sample |>
  select(side,sample) |> 
  mutate(sum = sum(sample), 
         prop_sample = 100*(sample / sum)) |>
  select(-sum)   



diff <- 
  sample |> 
  pivot_longer(cols = c(general,sample), names_to = "group", values_to = "n") |>
  group_by(group) |>
  mutate(sum = sum(n)) |>
  pcit() |> 
  compare_proportions_by() |> 
  select(side=group, prop_diff,adj_p_value) |>
  mutate(prop_diff = 100*prop_diff) |>
  mutate_round(digits = 2)

gp |> 
  left_join(smp, by = "side") |>
  mutate(prop = 100*(sample / general)) |> 
  mutate_round(digits = 2) |> 
  left_join(diff, by = "side") |>
  mutate(general = paste0(general," (",prop_gp,"%)"),
         sample = paste0(sample," (",prop_sample,"%)")) |>
  knitr::kable()


bg <- read_excel("bg-data.xlsx") |> 
  filter(male != "NA") |>
  mutate(across(where(~ all(grepl("^[0-9]+$", .))), as.numeric))

######---Demographics---######


# bg |>
#   select(institution_1,5:15) |> 
#   tbl_summary() |> 
#   as_kable()


# bg |>
#   select(institution_1,5:15) |> 
#   to_dummmy() |> 
#   tbl_summary(by = male) |> 
#   add_difference() |>
#   as_kable()


# bg |>
#   select(institution_1,5:15) |> 
#   to_dummmy() |> 
#   tbl_summary(by = institution_1_df__var__Изпълнителна) |> 
#   add_difference() |>
#   as_kable()

bg |>
  select(male) |>
  table() |>
  rstatix::chisq_test() 

bg |>
  select(8:15) |>
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |>
  filter(value == 1) |> 
  select(var) |> 
  table() |>
  rstatix::chisq_test() |> 
  mutate_round()

bg |>
  select(8:15) |>
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |>
  filter(value == 1) |> 
  select(var) |> 
  table() |>
  rstatix::cramer_v()

bg |>
  select(8:15) |>
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |>
  filter(value == 1) |> 
  select(var) |> 
  count(var) |>
  mutate(sum = sum(n)) |>
  pcit() |>
  compare_proportions()


bg |> 
  select(social_services, institution_1) |> 
  table() |>
  effectsize::cramers_v()
  #rstatix::chisq_test()
  
bg |> 
  effectsize::cohens_d(experience ~ law, data = _)

bg |> 
  select(16,17) |> 
  get_summary_stats()

bg |> 
  select(institution_1, 16,17) |> 
  group_by(institution_1) |> 
  get_summary_stats()

bg |> 
  select(16,17) |> 
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |>
  count(var, value) |>
  group_by(var) |>
  mutate(sum = sum(n), 
         prop = (n / sum)) |>
  mutate(value = factor(value)) |> 
  ggplot(aes(x = prop, y = var, fill = value)) +
  geom_col(
    alpha = 0.7,
    position = position_likert()) +
  annotate("rect", 
           xmin=c(0, 0),
           xmax = c(0.5, 0.65),
           ymin = c(1.5, 0.5),
           ymax = c(2.5, 1.48),
           color = "black",
           size = 0.3,
           lty = 2,
           fill = "#BDE8CA",
           alpha = 0.3) +
  geom_text(
    aes(label = paste0("(", value, ")   ", scales::percent(prop))),
    position = position_likert(vjust = 0.5),
    size = 6,
    angle = 90,
    family = "Sofia Sans Condensed",
    fontface = "bold",
  ) +
  scale_fill_manual(values = c("3" = "gray90", 
                               "1" = "#C7253E",
                               "2" = "#E85C0D",
                               "4" = "#41B3A2",
                               "5" = "#0D7C66"))+
  scale_x_continuous(
    label = label_percent_abs(),
    limits = c(-0.6, 1),
    breaks = seq(-.6, .6, by = 0.2))+
  scale_y_discrete(
    labels = c("awareness_interest" = "Информираност",
               "power" = "Влияние"))+
  guides(
    x = guide_axis(cap = "both"), # Cap both ends
    y = guide_axis(cap = "both") # Cap the upper end
  ) +
  annotate("text",
           x = c(0.6, 0.75),
           y = c(2, 1),
           label = c("47.28%", "60.45%") ,
           color = "darkgreen",
           size=7, 
           angle = 0,
           family = "Sofia Sans Condensed")+
  theme(axis.line = element_line(), 
        legend.position = "none")+
  labs(
    x = "",
    y = ""
  )
  
  
# ggsave(
#   "inform-power-bg.png",
#   units = "mm",
#   bg = "white",
#   width = 280,
#   height = 140,
#   dpi = 1000
# )

bg |> 
  select(16,17) |> 
  get_summary_stats() |> 
  mutate(
    LCI = mean - ci, 
    UCI = mean + ci) |>
  select(variable, mean, LCI, UCI) 

bg |> 
  select(16,17) |> 
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |>
  t_test(value ~ var) 


bg |> 
  select(16,17) |> 
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |>
  effectsize::cohens_d(value ~ var, data = _)

bg |> 
  select(institution_1, 16,17) |> 
  pivot_longer(cols = 2:3, names_to = "var", values_to = "value") |>
  mutate(fct_var = case_when(
    value == 1 ~ "no",
    value == 2 ~ "no",
    value == 3 ~ "both",
    value == 4 ~ "yes",
    value == 5 ~ "yes")) |> 
  count(var,institution_1,fct_var) |>
  group_by(var, institution_1) |>
  mutate(sum = sum(n)) |>
  filter(fct_var == "yes") |>
  select(-fct_var) |>
  pcit() |> 
  compare_proportions_by() |> 
  mutate_round(digits = 5) |> 
  filter(adj_p_value < 0.05) 
  

bg |> 
  select(institution_1, 16,17) |> 
  pivot_longer(cols = 2:3, names_to = "var", values_to = "value") |>
  mutate(fct_var = case_when(
    value == 1 ~ "no",
    value == 2 ~ "no",
    value == 3 ~ "both",
    value == 4 ~ "yes",
    value == 5 ~ "yes")) |> 
  count(var,institution_1,fct_var) |>
  group_by(var, institution_1) |>
  mutate(sum = sum(n)) |>
  filter(fct_var == "yes") |>
  select(-fct_var) |>
  pcit() |> 
  select(var,institution_1, proportion) |> 
  pivot_wider(names_from = var, values_from = proportion) |>
  mutate(awareness_interest  = replace_na(awareness_interest, 0),
         power = replace_na(power, 0)) |> 
  mutate(ratio = awareness_interest / power) 


inf <- 
  bg |> 
  count(institution_1, awareness_interest) |>
  group_by(institution_1) |>
  mutate(sum = sum(n), 
         prop = (n / sum)) |>
  mutate(awareness_interest = factor(awareness_interest)) |> 
  ggplot(aes(x = prop, y = institution_1, fill = awareness_interest)) +
  geom_col(
    width = 0.9,
    alpha = 0.7,
    position = "likert_count") +
  geom_text(
    aes(label = paste0("(", awareness_interest, ")   ", scales::percent(prop))),
    position = position_likert(vjust = 0.5),
    size = 5,
    angle = 90,
    family = "Sofia Sans Condensed",
  ) +
  scale_fill_manual(values = c("3" = "gray90", 
                               "1" = "#C7253E",
                               "2" = "#E85C0D",
                               "4" = "#41B3A2",
                               "5" = "#0D7C66"))+
  scale_x_continuous(
    label = label_percent_abs(),
    limits = c(-0.8, .8),
    breaks = seq(-.6, .6, by = 0.2))+
  scale_y_discrete(
    labels = c(
    "Академия" = "Академия",                   
    "Законодателна" = "Законодателна власт",              
    "Изпълнителна" = "Изпълнителна власт",               
    "Индустрия" = "Индустрия",                  
    "Научни дружества" = "Научни дружества",           
    "Пациентски организации" = "Пациентски организации",     
    "Съсловни организации" = "Съсловни организации"))+       
  guides(
    x = guide_axis(cap = "both"), # Cap both ends
    y = guide_axis(cap = "both") # Cap the upper end
  ) +
  theme(axis.line = element_line(), 
        axis.text.x = element_text(angle = 0, 
                                   vjust = 1, 
                                   hjust = 1),
        legend.position = "none")+
  labs(
    x = "Информираност",
    y = ""
  )


pwr <- 
  bg |> 
  count(institution_1, power) |>
  group_by(institution_1) |>
  mutate(sum = sum(n), 
         prop = (n / sum)) |>
  mutate(power = factor(power)) |> 
  ggplot(aes(x = prop, y = institution_1, fill = power)) +
  geom_col(
    width = 0.9,
    alpha = 0.7,
    position = "likert_count") +
  geom_text(
    aes(label = paste0("(", power, ")   ", scales::percent(prop))),
    position = position_likert(vjust = 0.5),
    size = 5,
    angle = 90,
    family = "Sofia Sans Condensed",
  ) +
  scale_fill_manual(values = c("3" = "gray90", 
                               "1" = "#C7253E",
                               "2" = "#E85C0D",
                               "4" = "#41B3A2",
                               "5" = "#0D7C66"))+
  scale_x_continuous(
    label = label_percent_abs(),
    limits = c(-0.8, .8),
    breaks = seq(-.6, .6, by = 0.2))+
  scale_y_discrete(
    labels = c(
      "Академия" = "Академия",                   
      "Законодателна" = "Законодателна власт",              
      "Изпълнителна" = "Изпълнителна власт",               
      "Индустрия" = "Индустрия",                  
      "Научни дружества" = "Научни дружества",           
      "Пациентски организации" = "Пациентски организации",     
      "Съсловни организации" = "Съсловни организации"))+       
  guides(
    x = guide_axis(cap = "both"), # Cap both ends
    y = guide_axis(cap = "both") # Cap the upper end
  ) +
  theme(
    axis.line= element_line(), 
    legend.position = "none")+
  labs(
    x = "Влияние",
    y = ""
  )


inf/pwr

# ggsave(
#   "inform-power-by-side-bg.png",
#   units = "mm",
#   bg = "white",
#   width = 300,
#   height = 400,
#   dpi = 1000
# )

######---Definition---######

  bg |> 
  select(18:21) |> 
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |>
  count(var, value) |>
  group_by(var) |>
  mutate(sum = sum(n), 
         prop = (n / sum)) |>
  mutate(value = factor(value)) |> 
  ggplot(aes(x = prop, y = var, fill = value)) +
  geom_col(
    alpha = 0.7,
    position = position_likert()) +
  annotate("rect", 
           xmin=c(0, 0, 0, 0),
           xmax = c(0.35, 0.55, 0.37, 0.3),
           ymin = c(0.5, 1.5, 2.5, 3.5),
           ymax = c(1.5, 2.5, 3.5, 4.5),
           color = "black",
           size = 0.3,
           lty = 2,
           fill = "#BDE8CA",
           alpha = 0.3) +
  geom_text(
    aes(label =ifelse(prop > 0.15, 
                      scales::percent(prop),
                      "")),
    position = position_likert(vjust = 0.5),
    size = 6,
    fontface = "bold",
    angle = 0,
    family = "Sofia Sans Condensed",
  ) +
  geom_text(
    aes(label =ifelse(prop <= 0.15, 
                      scales::percent(prop),
                      "")),
    position = position_likert(vjust = 0.5),
    size = 6,
    fontface = "bold",
    angle = 90,
    family = "Sofia Sans Condensed",
  )+
  geom_vline(xintercept = 0, 
             linetype = 2,
             size = 0.2,
             color = "gray80") +
  scale_fill_manual(values = c("3" = "gray90", 
                               "1" = "#C7253E",
                               "2" = "#E85C0D",
                               "4" = "#41B3A2",
                               "5" = "#0D7C66"))+
  scale_x_continuous(
    label = label_percent_abs(),
    limits = c(-0.75, 0.75),
    breaks = seq(-.6, .6, by = 0.2))+
  scale_y_discrete(
    labels = c(
    "def_balanced" = "Балансирана (I = 6/100000)",
    "def_conservative" = "Консервативна (I < 6/100000)",
    "def_liberal" = "Либерална (I > 6/100000)",  
    "def_status_quo" = "Статукво - дефиниция за РБ"))+
  guides(
    x = guide_axis(cap = "both"), # Cap both ends
    y = guide_axis(cap = "both") # Cap the upper end
  ) +
  annotate("text",
           x = c(0.7, 0.7, 0.7, 0.7),
           y = c(1, 2, 3, 4),
           label = c("34.1%", "54.3%", "36.8%", "29.5%") ,
           color = "darkgreen",
           size=7, 
           angle = 0,
           family = "Sofia Sans Condensed")+
  theme(axis.line = element_line(), 
        axis.text = element_text(family = "Sofia Sans Condensed", size = 24),
        legend.position = "none")+
  labs(
    x = "",
    y = ""
  )


 ggsave(
   "def-bg.png",
   units = "mm",
   bg = "white",
   width = 300,
   height = 150,
   dpi = 1000
 )


  bg |> 
  select(18:21) |> 
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
  group_by(var) |>
  get_summary_stats() |>
  ggplot(aes(x = mean, y = fct_reorder(var, mean))) +
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
    xintercept = 2.61,
    lty = 2,
    size = 0.5,
    color = "gray10"
  ) +
  scale_y_discrete(
      labels = c(
        "def_balanced" = "Балансирана (I = 6/100000)",
        "def_conservative" = "Консервативна (I < 6/100000)",
        "def_liberal" = "Либерална (I > 6/100000)",  
        "def_status_quo" = "Статукво - дефиниция за РБ"))+
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
#   "def-mean-bg.png",
#   units = "mm",
#   bg = "white",
#   width = 300,
#   height = 120,
#   dpi = 1000
# )
  
  
  
  
bg |> 
  select(18:21) |> 
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
      Parameter1 = case_when(
        Parameter1 == "def_balanced" ~ "Балансирана (I = 6/100000)",
        Parameter1 == "def_conservative" ~ "Консервативна (I < 6/100000)",
        Parameter1 == "def_liberal" ~ "Либерална (I > 6/100000)",  
        Parameter1 == "def_status_quo" ~ "Статукво - дефиниция за РБ"
      ),
      Parameter2 = case_when(
        Parameter2 == "def_balanced" ~ "Балансирана (I = 6/100000)",
        Parameter2 == "def_conservative" ~ "Консервативна (I < 6/100000)",
        Parameter2 == "def_liberal" ~ "Либерална (I > 6/100000)",  
        Parameter2 == "def_status_quo" ~ "Статукво - дефиниция за РБ"),
      p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ ""))|>
    filter(Parameter1 != Parameter2) |>
    filter(Parameter1 > Parameter2) |>
    ggplot(aes(Parameter1, Parameter2, fill = r)) +
    geom_tile(color = "gray10") +
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
              fontface = "bold",
              size = 8) +
    theme() +
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
#   "def-full-corr-bg.png",
#   units = "mm",
#   bg = "white",
#   width = 320,
#   height = 140,
#   dpi = 1000
# )


bg |> 
  select(18:21) |> 
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
  group_by(var) |>
  get_summary_stats() |> 
  mutate(
    LCI = mean - ci, 
    UCI = mean + ci) |>
  select(var, mean, LCI, UCI)

bg |> 
  select(18:21) |> 
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
  mutate(agreement =
           case_when(
             value == 1 ~ "Disagree",
             value == 2 ~ "Disagree",
             value == 3 ~ "Neutral",
             value == 4 ~ "Agree",
             value == 5 ~ "Agree")) |> 
  count(var, agreement) |>
  pivot_wider(names_from = agreement, values_from = n) |>
  mutate(agr = Agree + 0.5*Neutral) |>
  select(var, agr) |>
  mutate(sum = 110) |> 
  ungroup() |> 
  mutate(agr = as.integer(agr), 
         sum = as.integer(sum)) |>
  pcit()

bg |> 
  select(18:21) |> 
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
  aov(value ~ var, data = _) |>
  emmeans::emmeans(pairwise ~ "var", 
                   mode = "eff.size", 
                   adjust = "bonferroni") 

bg |> 
  select(18:21) |> 
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
  mutate(agreement =
           case_when(
             value == 1 ~ "Disagree",
             value == 2 ~ "Disagree",
             value == 3 ~ "Neutral",
             value == 4 ~ "Agree",
             value == 5 ~ "Agree")) |> 
  count(var, agreement) |>
  pivot_wider(names_from = agreement, values_from = n) |>
  mutate(agr = Agree + 0.5*Neutral) |>
  select(var, agr) |>
  mutate(sum = 110) |> 
  ungroup() |> 
  mutate(agr = as.integer(agr), 
         sum = as.integer(sum)) |> 
  select(var, agr) |>
  pivot_wider(names_from = var, values_from = agr) |>
  rstatix::chisq_test() 

  
bg |> 
  select(18:21) |> 
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
  mutate(agreement =
           case_when(
             value == 1 ~ "Disagree",
             value == 2 ~ "Disagree",
             value == 3 ~ "Neutral",
             value == 4 ~ "Agree",
             value == 5 ~ "Agree")) |> 
  count(var, agreement) |>
  pivot_wider(names_from = agreement, values_from = n) |>
  mutate(agr = Agree + 0.5*Neutral) |>
  select(var, agr) |>
  mutate(sum = 110) |> 
  ungroup() |> 
  mutate(agr = as.integer(agr), 
         sum = as.integer(sum)) |>
  pcit() |> 
  compare_proportions() |> 
  mutate_round(digits = 2) |>
  filter(adj_p_value < 0.05)

bg |>
  select(18:21) |>
  rowwise() %>%
  mutate(diff = {
    sorted_values <- sort(c_across(everything()), decreasing = TRUE)
    sorted_values[1] - sorted_values[2]
  }) %>%
  ungroup() |> 
  mutate(row = row_number()) |>
  pivot_longer(cols = 1:4, names_to = "var", values_to = "value") |>
  slice_max(by = row, value, n = 2) |>
  group_by(row) |> 
  mutate(alternatives = paste0(var, collapse = " vs. ")) |>
  ungroup() |> 
  count(diff, alternatives) |> 
  separate(alternatives, into = paste0("alt_", 1:4), sep = " vs. ", fill = "right") |>
  group_by(alt_1) |> 
  summarise(
    n = sum(n),
    sum = sum(diff),
    distance = sum(diff)/n) |> 
  mutate(
    adr = ifelse(distance > 0.3, TRUE, FALSE)) |> 
  ggplot(aes(distance,fct_reorder(alt_1,distance), fill = adr)) +
  geom_col(color = "black")+
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.1f", distance * 100
    ), "%  ")),
    #color = agreement > .05
    #hjust = agreement > .05),
    hjust = "right",
    size = 6,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  scale_fill_manual(values = monochromeR::generate_palette("#37B7C3", 
                     modification = "go_both_ways", 
                     n_colours = 2))+
  geom_vline(
    xintercept = 0.3,
    lty = 2,
    size = 0.5,
    color = "#013440"
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(-0.05, 0.65),
    breaks = c(seq(0, 1, 0.2)),
    labels = scales::label_percent()
  ) +
  scale_y_discrete(
    labels = c(
      "def_balanced" = "Балансирана (I = 6/100000)",
      "def_conservative" = "Консервативна (I < 6/100000)",
      "def_liberal" = "Либерална (I > 6/100000)",  
      "def_status_quo" = "Статукво - дефиниция за РБ"))+
  guides(
    x = guide_axis(cap = "both"), # Cap both ends
    y = guide_axis(cap = "both") # Cap the upper end
  ) +
  theme(legend.position = "none",
        axis.line = element_line(),
        axis.text = element_text(
          family = "Sofia Sans Condensed", 
          size = 20)) +
  labs(y = "", x = "% Дистанциране")

# ggsave(
#   "def-distance-bg.png",
#   units = "mm",
#   bg = "white",
#   width = 240,
#   height = 120,
#   dpi = 1000
# )

bg |>
  select(18:21) |>
  rowwise() %>%
  mutate(diff = {
    sorted_values <- sort(c_across(everything()), decreasing = TRUE)
    sorted_values[1] - sorted_values[2]
  }) %>%
  ungroup() |> 
  mutate(row = row_number()) |>
  pivot_longer(cols = 1:4, names_to = "var", values_to = "value") |>
  slice_max(by = row, value, n = 2) |>
  group_by(row) |> 
  mutate(alternatives = paste0(var, collapse = " vs. ")) |>
  ungroup() |> 
  count(diff, alternatives) |> 
  separate(alternatives, into = paste0("alt_", 1:4), sep = " vs. ", fill = "right") |>
  group_by(alt_1) |>
  summarise(
    n = sum(n),
    sum = sum(diff)) |> 
  select(alt_1, distn = sum, sumn = n) |> 
  mutate(distn = as.integer(distn), 
         sumn = as.integer(sumn)) |>
  pcit() |>
  compare_proportions()
  
bg |> 
  select(16,17:21) |> 
  correlation::correlation(
    select = c("awareness_interest","power"), 
    select2 = c("def_conservative",
                "def_balanced",
                "def_liberal",
                "def_status_quo"), 
    method = "pearson") |>
  tibble() |> 
  filter(p < 0.05) 


bg |> 
  select(1,5:21) |> 
  mutate(
    stateholder = case_when(
      institution_1 == "Академия" ~ "Non-governmental",
      institution_1 == "Законодателна" ~ "Governmental",
      institution_1 == "Изпълнителна" ~ "Governmental",
      institution_1 == "Индустрия" ~ "Non-governmental",
      institution_1 == "Научни дружества" ~ "Non-governmental",
      institution_1 == "Пациентски организации" ~ "Non-governmental",
      institution_1 == "Съсловни организации" ~ "Non-governmental"
    )) |>
  pivot_longer(15:18, names_to = "var", values_to = "value") |>
  filter(var == "def_status_quo") |>
  mutate(
    value = as.factor(value)) |>
  select(-c(institution_1, var)) |>
  ordinal::clm(value ~ ., data = _) |> 
  tidy(exp = TRUE, conf.int = TRUE)


bg |>
  select(1, 5:21) |>
  mutate(
    goverment_sh = case_when(
      institution_1 == "Академия" ~ 0,
      institution_1 == "Законодателна" ~ 1,
      institution_1 == "Изпълнителна" ~ 1,
      institution_1 == "Индустрия" ~ 0,
      institution_1 == "Научни дружества" ~ 0,
      institution_1 == "Пациентски организации" ~ 0,
      institution_1 == "Съсловни организации" ~ 0
    )
  ) |>
  pivot_longer(15:18, names_to = "var", values_to = "value") |>
  mutate(value = as.factor(value)) |>
  mutate(goverment_sh = as.factor(goverment_sh)) |>
  select(-institution_1) |>
  group_by(var) |>
  nest() |>
  mutate(model = map(
    data,
    ~ .x |>
      ordinal::clm(value ~ ., data = _) |>
      tidy(exp = TRUE, conf.int = TRUE)
  )) |>
  unnest(model) |>
  filter(coef.type != "intercept") |>
  select(-c(data, coef.type)) |>
  filter(p.value < 0.05) |>
  mutate(
    CI = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
  ) |> 
  mutate_round(digits = 2) |> 
  knitr::kable()

bg |>
  select(1,5:21) |>
  pivot_longer(15:18, names_to = "var", values_to = "value") |>
  mutate(value = as.factor(value)) |>
  group_by(var) |>
  nest() |>
  mutate(model = map(
    data,
    ~ .x |>
      collect_ordinal_logistic_results(outcome = "value")))|>
  unnest(model) |>
  select(-data) |> 
  filter(p.value < 0.05) |>
  mutate(
    CI = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
  ) |> 
  mutate_round(digits = 2) |> 
  knitr::kable()


bg |>
  select(1,5:17,5:21) |> 
  to_dummmy() |> 
  pivot_longer(14:17, names_to = "var", values_to = "value") |>
  mutate(value = as.factor(value)) |> 
  group_by(var) |>
  nest() |>
  mutate(model = map(
    data,
    ~ .x |>
      collect_ordinal_logistic_results(outcome = "value")))|>
  unnest(model) |>
  select(-data) |> 
  filter(!is.na(conf.low)) |>
  mutate(
    CI = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
  ) |> 
  filter(p.value < 0.05) |>
  mutate_round(digits = 2) |> 
  select(-term) |> 
  knitr::kable()



set.seed(123)



# stateholders_def <- 
#   bg |>
#   select(1,5:15,18:21) |>
#   rsample::bootstraps(4000) |>
#   mutate(
#       prop = map(splits, ~ analysis(.x) |>
#                   pivot_longer(cols = 13:16, 
#                                 names_to = "var", 
#                                 values_to = "value") |>
#                    mutate(
#                      agrm = case_when(
#                        value == 1 ~ "Disagree",
#                        value == 2 ~ "Disagree",
#                        value == 3 ~ "Neutral",
#                        value == 4 ~ "Agree",
#                        value == 5 ~ "Agree")) |>
#                    count(institution_1 ,var,agrm) |> 
#                    pivot_wider(names_from = agrm, values_from = n) |>
#                    mutate_all(~replace_na(., 0)) |>
#                    mutate(agr = Agree + 0.5*Neutral, 
#                           sum = Agree + Disagree + Neutral,
#                           prop = agr/sum) |>
#                    select(-c(Disagree, Neutral, agr, sum, Agree))))


# stateholders_def |> 
#   unnest(prop) |> 
#   ggplot(aes(prop, 
#              fct_reorder(institution_1, prop))) +
#   stat_halfeye(aes(fill_ramp = after_stat(x > .5)), 
#                normalize = "groups", 
#                subguide = "none",
#                scale = 0.65,
#                fill = "#211C6A") +
#   geom_vline(xintercept = 0.5, 
#              linewidth = 0.5,
#              linetype = 2,
#              color = "gray10") +
#   scale_fill_ramp_discrete(from = "gray90", guide = "none") +
#   scale_x_continuous(expand = c(0, 0),
#                      limits = c(-0.1, 1.10), 
#                      labels = scales::label_percent(),
#                      breaks = c(seq(-1, 1, 0.2))) +
#   guides(
#     x = guide_axis(cap = "both"), # Cap both ends
#     y = guide_axis(cap = "both") # Cap the upper end
#   ) +
#   theme(legend.position = "none", 
#         axis.line = element_line())+
#   facet_wrap(~var, 
#              labeller = labeller(var = c(
#                def_balanced = "Балансирана (I = 6/100000)",
#                def_conservative = "Консервативна (I < 6/100000)",
#                def_liberal = "Либерална (I > 6/100000)",  
#                def_status_quo = "Статукво - дефиниция за РБ")))+
#   labs(x = "Разпределение на индекса на съгласие", y = "")

# ggsave(
#   "def-stateholders-bg.png",
#   units = "mm",
#   bg = "white",
#   width = 260,
#   height = 280,
#   dpi = 1000
# )

# stateholders_def |> 
#   unnest(prop) |>
#   group_by(var, institution_1) |>
#   summarise(
#     mean = mean(prop),
#     LCI = quantile(prop, 0.025), 
#     UCI = quantile(prop, 0.975)) |> 
#   mutate(CI = paste0(round(LCI, 2), ", ", round(UCI, 2))) |>
#   select(-c(LCI, UCI)) |>
#   mutate_round(digits = 2) |>
#   knitr::kable()



######---Organization---######


bg |> 
  select(22:25) |> 
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |>
  count(var, value) |>
  group_by(var) |>
  mutate(sum = sum(n), 
         prop = (n / sum)) |>
  mutate(value = factor(value)) |> 
  ggplot(aes(x = prop, y = var, fill = value)) +
  geom_col(
    alpha = 0.7,
    position = position_likert()) +
  annotate("rect", 
           xmin=c(0, 0, 0, 0),
           xmax = c(0.45, 0.5, 0.34, 0.56),
           ymin = c(0.5, 1.5, 2.5, 3.5),
           ymax = c(1.5, 2.5, 3.5, 4.5),
           color = "black",
           size = 0.3,
           lty = 2,
           fill = "#BDE8CA",
           alpha = 0.3) +
  geom_text(
    aes(label =ifelse(prop > 0.15, 
                      scales::percent(prop),
                      "")),
    position = position_likert(vjust = 0.5),
    size = 6,
    fontface = "bold",
    angle = 0,
    family = "Sofia Sans Condensed",
  ) +
  geom_text(
    aes(label =ifelse(prop <= 0.15, 
                      scales::percent(prop),
                      "")),
    position = position_likert(vjust = 0.5),
    size = 6,
    fontface = "bold",
    angle = 90,
    family = "Sofia Sans Condensed",
  )+
  geom_vline(xintercept = 0, 
             linetype = 2,
             size = 0.2,
             color = "gray80") +
  scale_fill_manual(values = c("3" = "gray90", 
                               "1" = "#C7253E",
                               "2" = "#E85C0D",
                               "4" = "#41B3A2",
                               "5" = "#0D7C66"))+
  scale_x_continuous(
    label = label_percent_abs(),
    limits = c(-0.75, 0.75),
    breaks = seq(-.6, .6, by = 0.2))+
  scale_y_discrete(
    labels = c(
    "organisation_balanced" = "Балансирана (Само КОЦ)",
    "organisation_conservative" = "Консервативна (Един център)",
    "organisation_liberal" = "Либерална (Всички ЛЗ)",
    "organisation_status_quo" = "Статукво"))+
  guides(
    x = guide_axis(cap = "both"), # Cap both ends
    y = guide_axis(cap = "both") # Cap the upper end
  ) +
  annotate("text",
           x = c(0.7, 0.7, 0.7, 0.7),
           y = c(1, 2, 3, 4),
           label = c("44.1%", "48.6%", "33.8%", "55%") ,
           color = "darkgreen",
           size=7, 
           angle = 0,
           family = "Sofia Sans Condensed")+
  theme(axis.line = element_line(), 
        axis.text = element_text(family = "Sofia Sans Condensed", size = 24),
        legend.position = "none")+
  labs(
    x = "",
    y = ""
  )


 ggsave(
   "org-bg.png",
   units = "mm",
   bg = "white",
   width = 300,
   height = 150,
   dpi = 1000
 )


bg |> 
  select(22:25) |> 
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
  group_by(var) |>
  get_summary_stats() |>
  ggplot(aes(x = mean, y = fct_reorder(var, mean))) +
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
    xintercept = 2.83,
    lty = 2,
    size = 0.5,
    color = "gray10"
  ) +
  scale_y_discrete(
    labels = c(
      "organisation_balanced" = "Балансирана (Само КОЦ)",
      "organisation_conservative" = "Консервативна (Един център)",
      "organisation_liberal" = "Либерална (Всички ЛЗ)",
      "organisation_status_quo" = "Статукво"))+
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
#   "org-mean-bg.png",
#   units = "mm",
#   bg = "white",
#   width = 300,
#   height = 120,
#   dpi = 1000
# )

bg |> 
  select(22:25) |> 
  correlation(redundant = TRUE) |>
  tibble() |>
  mutate(
    Parameter1 = case_when(
      Parameter1 == "organisation_balanced" ~ "Балансирана (Само КОЦ)",
      Parameter1 == "organisation_conservative" ~ "Консервативна (Един център)",
      Parameter1 == "organisation_liberal" ~"Либерална (Всички ЛЗ)",
      Parameter1 == "organisation_status_quo" ~ "Статукво"
    ),
    Parameter2 = case_when(
      Parameter2 == "organisation_balanced" ~ "Балансирана (Само КОЦ)",
      Parameter2 == "organisation_conservative" ~ "Консервативна (Един център)",
      Parameter2 == "organisation_liberal" ~ "Либерална (Всички ЛЗ)",
      Parameter2 == "organisation_status_quo" ~ "Статукво"),
    p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ ""))|>
  filter(Parameter1 != Parameter2) |>
  filter(Parameter1 > Parameter2) |>
  ggplot(aes(Parameter1, Parameter2, fill = r)) +
  geom_tile(color = "gray10") +
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
            fontface = "bold",
            size = 8) +
  theme() +
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
#   "org-full-corr-bg.png",
#   units = "mm",
#   bg = "white",
#   width = 320,
#   height = 140,
#   dpi = 1000
# )


bg |> 
  select(22:25) |> 
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
  group_by(var) |>
  get_summary_stats() |> 
  mutate(
    LCI = mean - ci, 
    UCI = mean + ci) |>
  select(var, mean, LCI, UCI)

bg |> 
  select(22:25) |> 
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
  mutate(agreement =
           case_when(
             value == 1 ~ "Disagree",
             value == 2 ~ "Disagree",
             value == 3 ~ "Neutral",
             value == 4 ~ "Agree",
             value == 5 ~ "Agree")) |> 
  count(var, agreement) |>
  pivot_wider(names_from = agreement, values_from = n) |>
  mutate(agr = Agree + 0.5*Neutral) |>
  select(var, agr) |>
  mutate(sum = 110) |> 
  ungroup() |> 
  mutate(agr = as.integer(agr), 
         sum = as.integer(sum)) |>
  pcit() |> 
  compare_proportions() 

bg |> 
  select(22:25) |>
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
  aov(value ~ var, data = _) |>
  emmeans::emmeans(pairwise ~ "var", 
                   mode = "eff.size", 
                   adjust = "bonferroni") 

bg |> 
  select(22:25) |>
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
  mutate(agreement =
           case_when(
             value == 1 ~ "Disagree",
             value == 2 ~ "Disagree",
             value == 3 ~ "Neutral",
             value == 4 ~ "Agree",
             value == 5 ~ "Agree")) |> 
  count(var, agreement) |>
  pivot_wider(names_from = agreement, values_from = n) |>
  mutate(agr = Agree + 0.5*Neutral) |>
  select(var, agr) |>
  mutate(sum = 110) |> 
  ungroup() |> 
  mutate(agr = as.integer(agr), 
         sum = as.integer(sum)) |> 
  select(var, agr) |>
  pivot_wider(names_from = var, values_from = agr) |>
  rstatix::chisq_test() 


bg |> 
  select(22:25) |>  
  pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
  mutate(agreement =
           case_when(
             value == 1 ~ "Disagree",
             value == 2 ~ "Disagree",
             value == 3 ~ "Neutral",
             value == 4 ~ "Agree",
             value == 5 ~ "Agree")) |> 
  count(var, agreement) |>
  pivot_wider(names_from = agreement, values_from = n) |>
  mutate(agr = Agree + 0.5*Neutral) |>
  select(var, agr) |>
  mutate(sum = 110) |> 
  ungroup() |> 
  mutate(agr = as.integer(agr), 
         sum = as.integer(sum)) |>
  pcit() |> 
  compare_proportions() |> 
  mutate_round(digits = 2) |>
  filter(adj_p_value < 0.05)

bg |>
  select(22:25) |> 
  rowwise()  |> 
  mutate(diff = {
    sorted_values <- sort(c_across(everything()), decreasing = TRUE)
    sorted_values[1] - sorted_values[2]
  }) %>%
  ungroup() |> 
  mutate(row = row_number()) |>
  pivot_longer(cols = 1:4, names_to = "var", values_to = "value") |>
  slice_max(by = row, value, n = 2) |>
  group_by(row) |> 
  mutate(alternatives = paste0(var, collapse = " vs. ")) |>
  ungroup() |> 
  count(diff, alternatives) |> 
  separate(alternatives, into = paste0("alt_", 1:4), sep = " vs. ", fill = "right") |>
  group_by(alt_1) |> 
  summarise(
    n = sum(n),
    sum = sum(diff),
    distance = sum(diff)/n) |> 
  mutate(
    adr = ifelse(distance > 0.302, TRUE, FALSE)) |> 
  ggplot(aes(distance,fct_reorder(alt_1,distance), fill = adr)) +
  geom_col(color = "black")+
  geom_text(
    aes(label = paste0("  ", sprintf(
      "%2.1f", distance * 100
    ), "%  ")),
    #color = agreement > .05
    #hjust = agreement > .05),
    hjust = "right",
    size = 6,
    fontface = "bold",
    family = "Roboto Condensed",
  ) +
  scale_fill_manual(values = monochromeR::generate_palette("#37B7C3", 
                                                           modification = "go_both_ways", 
                                                           n_colours = 2))+
  geom_vline(
    xintercept = 0.3,
    lty = 2,
    size = 0.5,
    color = "#013440"
  ) +
  scale_x_continuous(
    expand = c(0, 0),
    limits = c(-0.05, 0.45),
    breaks = c(seq(0, 1, 0.1)),
    labels = scales::label_percent()
  ) +
  scale_y_discrete(
    labels = c(
      "organisation_balanced" = "Балансирана (Само КОЦ)",
      "organisation_conservative" = "Консервативна (Един център)",
      "organisation_liberal" = "Либерална (Всички ЛЗ)",
      "organisation_status_quo" = "Статукво"))+
  guides(
    x = guide_axis(cap = "both"), # Cap both ends
    y = guide_axis(cap = "both") # Cap the upper end
  ) +
  theme(legend.position = "none",
        axis.line = element_line(),
        axis.text = element_text(
          family = "Sofia Sans Condensed", 
          size = 20)) +
  labs(y = "", x = "% Дистанциране")

# ggsave(
#   "org-distance-bg.png",
#   units = "mm",
#   bg = "white",
#   width = 240,
#   height = 120,
#   dpi = 1000
# )

bg |>
  select(22:25) |> 
  rowwise() %>%
  mutate(diff = {
    sorted_values <- sort(c_across(everything()), decreasing = TRUE)
    sorted_values[1] - sorted_values[2]
  }) %>%
  ungroup() |> 
  mutate(row = row_number()) |>
  pivot_longer(cols = 1:4, names_to = "var", values_to = "value") |>
  slice_max(by = row, value, n = 2) |>
  group_by(row) |> 
  mutate(alternatives = paste0(var, collapse = " vs. ")) |>
  ungroup() |> 
  count(diff, alternatives) |> 
  separate(alternatives, into = paste0("alt_", 1:4), sep = " vs. ", fill = "right") |>
  group_by(alt_1) |>
  summarise(
    n = sum(n),
    sum = sum(diff)) |> 
  select(alt_1, distn = sum, sumn = n) |> 
  mutate(distn = as.integer(distn), 
         sumn = as.integer(sumn)) |>
  pcit() |>
  compare_proportions()


bg |> 
  select(16,17, 22:25) |> 
  correlation::correlation(
    select = c("awareness_interest","power"), 
    select2 = c("organisation_conservative",
                "organisation_balanced",
                "organisation_liberal",
                "organisation_status_quo"), 
    method = "pearson") |>
  tibble() |> 
  filter(p < 0.05) 


bg |> 
  select(1,5:17,22:25) |> 
  mutate(
    stateholder = case_when(
      institution_1 == "Академия" ~ "Non-governmental",
      institution_1 == "Законодателна" ~ "Governmental",
      institution_1 == "Изпълнителна" ~ "Governmental",
      institution_1 == "Индустрия" ~ "Non-governmental",
      institution_1 == "Научни дружества" ~ "Non-governmental",
      institution_1 == "Пациентски организации" ~ "Non-governmental",
      institution_1 == "Съсловни организации" ~ "Non-governmental"
    )) |>
  pivot_longer(15:18, names_to = "var", values_to = "value") |>
  filter(var == "organisation_status_quo") |>
  mutate(
    value = as.factor(value)) |>
  select(-c(institution_1, var)) |>
  ordinal::clm(value ~ ., data = _) |> 
  tidy(exp = TRUE, conf.int = TRUE)


bg |>
  select(1,5:17,22:25) |> 
  mutate(
    goverment_sh = case_when(
      institution_1 == "Академия" ~ 0,
      institution_1 == "Законодателна" ~ 1,
      institution_1 == "Изпълнителна" ~ 1,
      institution_1 == "Индустрия" ~ 0,
      institution_1 == "Научни дружества" ~ 0,
      institution_1 == "Пациентски организации" ~ 0,
      institution_1 == "Съсловни организации" ~ 0
    )
  ) |>
  pivot_longer(15:18, names_to = "var", values_to = "value") |>
  mutate(value = as.factor(value)) |>
  mutate(goverment_sh = as.factor(goverment_sh)) |>
  select(-institution_1) |>
  group_by(var) |>
  nest() |>
  mutate(model = map(
    data,
    ~ .x |>
      ordinal::clm(value ~ ., data = _) |>
      tidy(exp = TRUE, conf.int = TRUE)
  )) |>
  unnest(model) |>
  filter(coef.type != "intercept") |>
  select(-c(data, coef.type)) |>
  filter(p.value < 0.05) |>
  mutate(
    CI = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
  ) |> 
  mutate_round(digits = 2) |> 
  knitr::kable()



bg |>
  select(1,5:17,22:25) |> 
  to_dummmy() |> 
  pivot_longer(14:17, names_to = "var", values_to = "value") |>
  mutate(value = as.factor(value)) |> 
  group_by(var) |>
  nest() |>
  mutate(model = map(
    data,
    ~ .x |>
      collect_ordinal_logistic_results(outcome = "value")))|>
  unnest(model) |>
  select(-data) |> 
  filter(!is.na(conf.low)) |>
  mutate(
    CI = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
  ) |> 
  filter(p.value < 0.05) |>
  mutate_round(digits = 2) |> 
  select(-term) |> 
  knitr::kable()

 set.seed(123)
 
 

# stateholders_org <- 
#  bg |>
#  select(1,5:15,22:25) |>
#  rsample::bootstraps(4000) |>
#  mutate(
#      prop = map(splits, ~ analysis(.x) |>
#                  pivot_longer(cols = 13:16, 
#                                names_to = "var", 
#                                values_to = "value") |>
#                   mutate(
#                     agrm = case_when(
#                       value == 1 ~ "Disagree",
#                       value == 2 ~ "Disagree",
#                       value == 3 ~ "Neutral",
#                       value == 4 ~ "Agree",
#                       value == 5 ~ "Agree")) |>
#                   count(institution_1 ,var,agrm) |> 
#                   pivot_wider(names_from = agrm, values_from = n) |>
#                   mutate_all(~replace_na(., 0)) |>
#                   mutate(agr = Agree + 0.5*Neutral, 
#                          sum = Agree + Disagree + Neutral,
#                          prop = agr/sum) |>
#                   select(-c(Disagree, Neutral, agr, sum, Agree)))) 



#  stateholders_org |> 
#    unnest(prop) |> 
#    ggplot(aes(prop, 
#               fct_reorder(institution_1, prop))) +
#    stat_halfeye(aes(fill_ramp = after_stat(x > .5)), 
#                 normalize = "groups", 
#                 subguide = "none",
#                 scale = 0.65,
#                 fill = "#211C6A") +
#    geom_vline(xintercept = 0.5, 
#               linewidth = 0.5,
#               linetype = 2,
#               color = "gray10") +
#    scale_fill_ramp_discrete(from = "gray90", guide = "none") +
#    scale_x_continuous(expand = c(0, 0),
#                       limits = c(-0.1, 1.10), 
#                       labels = scales::label_percent(),
#                       breaks = c(seq(-1, 1, 0.2))) +
#    guides(
#      x = guide_axis(cap = "both"), # Cap both ends
#      y = guide_axis(cap = "both") # Cap the upper end
#    ) +
#    theme(legend.position = "none", 
#          axis.line = element_line())+
#    facet_wrap(~var, 
#               labeller = labeller(var = c(
#                 organisation_balanced = "Балансирана (Само КОЦ)",
#                 organisation_conservative = "Консервативна (Един център)",
#                 organisation_liberal = "Либерална (Всички ЛЗ)",
#                 organisation_status_quo = "Статукво")))+
#    labs(x = "Разпределение на индекса на съгласие", y = "")

# ggsave(
#   "org-stateholders-bg.png",
#   units = "mm",
#   bg = "white",
#   width = 260,
#   height = 280,
#   dpi = 1000
# )

# stateholders_org |> 
#   unnest(prop) |>
#   group_by(var, institution_1) |>
#   summarise(
#     mean = median(prop),
#     LCI = quantile(prop, 0.025), 
#     UCI = quantile(prop, 0.975)) |> 
#   mutate(CI = paste0(round(LCI, 2), ", ", round(UCI, 2))) |>
#   select(-c(LCI, UCI)) |>
#   mutate_round(digits = 2) |>
#   knitr::kable()

######---Medicines---######

 bg |> 
   select(26:29) |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |>
   count(var, value) |>
   group_by(var) |>
   mutate(sum = sum(n), 
          prop = (n / sum)) |>
   mutate(value = factor(value)) |> 
   ggplot(aes(x = prop, y = var, fill = value)) +
   geom_col(
     alpha = 0.7,
     position = position_likert()) +
   annotate("rect", 
            xmin=c(0, 0, 0, 0),
            xmax = c(0.79, 0.44, 0.42, 0.31),
            ymin = c(0.5, 1.5, 2.5, 3.5),
            ymax = c(1.5, 2.5, 3.5, 4.5),
            color = "black",
            size = 0.3,
            lty = 2,
            fill = "#BDE8CA",
            alpha = 0.3) +
   geom_text(
     aes(label =ifelse(prop > 0.1, 
                       scales::percent(prop),
                       "")),
     position = position_likert(vjust = 0.5),
     size = 6,
     angle = 0,
     family = "Sofia Sans Condensed",
   ) +
   geom_text(
     aes(label =ifelse(prop < 0.1, 
                       scales::percent(prop),
                       "")),
     position = position_likert(vjust = 0.5),
     size = 6,
     angle = 90,
     family = "Sofia Sans Condensed",
   )+
   geom_vline(xintercept = 0, 
              linetype = 2,
              size = 0.2,
              color = "gray80") +
   scale_fill_manual(values = c("3" = "gray90", 
                                "1" = "#C7253E",
                                "2" = "#E85C0D",
                                "4" = "#41B3A2",
                                "5" = "#0D7C66"))+
   scale_x_continuous(
     label = label_percent_abs(),
     limits = c(-0.85, 0.85),
     breaks = seq(-.8, .8, by = 0.2))+
   scale_y_discrete(
     labels = c(
        "newmed_balanced" = "Балансирана (QALY & PFS)",
        "newmed_conservative" = "Консервативна (YLG)",
        "newmed_liberal" = "Либерална (Пациентски критерии)",
        "newmed_status_quo" = "Статукво"))+
   guides(
     x = guide_axis(cap = "both"), # Cap both ends
     y = guide_axis(cap = "both") # Cap the upper end
   ) +
   annotate("text",
            x = c(0.85, 0.85, 0.85, 0.85),
            y = c(1, 2, 3, 4),
            label = c("78.8%", "43.1%", "41.4%", "30%") ,
            color = "darkgreen",
            size=7, 
            angle = 0,
            family = "Sofia Sans Condensed")+
   theme(axis.line = element_line(), 
         axis.text = element_text(family = "Sofia Sans Condensed", size = 24),
         legend.position = "none")+
   labs(
     x = "",
     y = ""
   )
 
 
  ggsave(
    "med-bg.png",
    units = "mm",
    bg = "white",
    width = 400,
    height = 200,
    dpi = 1000
  )
 
 
 bg |> 
   select(26:29) |>  
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   group_by(var) |>
   get_summary_stats() |>
   ggplot(aes(x = mean, y = fct_reorder(var, mean))) +
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
     xintercept = 2.83,
     lty = 2,
     size = 0.5,
     color = "gray10"
   ) +
   scale_y_discrete(
     labels = c(
       "newmed_balanced" = "Балансирана (QALY & PFS)",
       "newmed_conservative" = "Консервативна (YLG)",
       "newmed_liberal" = "Либерална (Пациентски критерии)",
       "newmed_status_quo" = "Статукво"))+
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
 
 
#  ggsave(
#    "med-mean-bg.png",
#    units = "mm",
#    bg = "white",
#    width = 300,
#    height = 120,
#    dpi = 1000
#  )

 

 

  
 bg |> 
   select(26:29) |> 
   correlation(redundant = TRUE) |>
   tibble() |>
   mutate(
     Parameter1 = case_when(
       Parameter1 == "newmed_balanced" ~ "Балансирана (QALY & PFS)",
       Parameter1 == "newmed_conservative" ~ "Консервативна (YLG)",
       Parameter1 == "newmed_liberal" ~ "Либерална (Пациентски критерии)",
       Parameter1 == "newmed_status_quo" ~ "Статукво"
     ),
     Parameter2 = case_when(
       Parameter2 == "newmed_balanced" ~ "Балансирана (QALY & PFS)",
       Parameter2 == "newmed_conservative" ~"Консервативна (YLG)",
       Parameter2 == "newmed_liberal" ~ "Либерална (Пациентски критерии)",
       Parameter2 == "newmed_status_quo" ~"Статукво"),
     p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ ""))|>
   filter(Parameter1 != Parameter2) |>
   filter(Parameter1 > Parameter2) |>
   ggplot(aes(Parameter1, Parameter2, fill = r)) +
   geom_tile(color = "gray10") +
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
             fontface = "bold",
             size = 8) +
   theme() +
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
 #   "med-full-corr-bg.png",
 #   units = "mm",
 #   bg = "white",
 #   width = 320,
 #   height = 140,
 #   dpi = 1000
 # )
 
 bg |> 
   select(26:29) |> 
   correlation(redundant = TRUE) |>
   tibble() |>
   mutate(
     Parameter1 = case_when(
       Parameter1 == "newmed_balanced" ~ "Балансирана (QALY & PFS)",
       Parameter1 == "newmed_conservative" ~ "Консервативна (YLG)",
       Parameter1 == "newmed_liberal" ~ "Либерална (Пациентски критерии)",
       Parameter1 == "newmed_status_quo" ~ "Статукво"
     ),
     Parameter2 = case_when(
       Parameter2 == "newmed_balanced" ~ "Балансирана (QALY & PFS)",
       Parameter2 == "newmed_conservative" ~"Консервативна (YLG)",
       Parameter2 == "newmed_liberal" ~ "Либерална (Пациентски критерии)",
       Parameter2 == "newmed_status_quo" ~"Статукво"),
     p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ ""))|>
   filter(Parameter1 != Parameter2) |>
   filter(Parameter1 > Parameter2) |> 
 mutate_round() |> 
   filter(p<0.05) |>
   select(-Method) |>
   knitr::kable()
 
 bg |> 
   select(26:29) |> 
   correlation(redundant = TRUE) |>
   tibble() |>
   mutate(
     Parameter1 = case_when(
       Parameter1 == "newmed_balanced" ~ "Балансирана (QALY & PFS)",
       Parameter1 == "newmed_conservative" ~ "Консервативна (YLG)",
       Parameter1 == "newmed_liberal" ~ "Либерална (Пациентски критерии)",
       Parameter1 == "newmed_status_quo" ~ "Статукво"
     ),
     Parameter2 = case_when(
       Parameter2 == "newmed_balanced" ~ "Балансирана (QALY & PFS)",
       Parameter2 == "newmed_conservative" ~"Консервативна (YLG)",
       Parameter2 == "newmed_liberal" ~ "Либерална (Пациентски критерии)",
       Parameter2 == "newmed_status_quo" ~"Статукво"),
     p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ ""))|>
   filter(Parameter1 != Parameter2) |>
   filter(Parameter1 > Parameter2) |>
   ggplot(aes(Parameter1, Parameter2, fill = r)) +
   geom_tile(color = "gray10") +
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
             fontface = "bold",
             size = 6) +
   theme() +
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
 #   "med-full-corr-bg.png",
 #   units = "mm",
 #   bg = "white",
 #   width = 320,
 #   height = 140,
 #   dpi = 1000
 # )
 
 
 bg |> 
   select(26:29) |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   group_by(var) |>
   get_summary_stats() |> 
   mutate(
     LCI = mean - ci, 
     UCI = mean + ci) |>
   select(var, mean, LCI, UCI)

 
 bg |> 
   select(26:29) |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   aov(value ~ var, data = _) |>
   emmeans::emmeans(pairwise ~ "var", 
                    mode = "eff.size", 
                    adjust = "bonferroni") 
 
 bg |> 
   select(26:29) |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   mutate(agreement =
            case_when(
              value == 1 ~ "Disagree",
              value == 2 ~ "Disagree",
              value == 3 ~ "Neutral",
              value == 4 ~ "Agree",
              value == 5 ~ "Agree")) |> 
   count(var, agreement) |>
   pivot_wider(names_from = agreement, values_from = n) |>
   mutate(agr = Agree + 0.5*Neutral) |>
   select(var, agr) |>
   mutate(sum = 110) |> 
   ungroup() |> 
   mutate(agr = as.integer(agr), 
          sum = as.integer(sum)) |> 
   select(var, agr) |>
   pivot_wider(names_from = var, values_from = agr) |>
   rstatix::chisq_test() 
 
 
 bg |> 
   select(26:29) |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   mutate(agreement =
            case_when(
              value == 1 ~ "Disagree",
              value == 2 ~ "Disagree",
              value == 3 ~ "Neutral",
              value == 4 ~ "Agree",
              value == 5 ~ "Agree")) |> 
   count(var, agreement) |>
   pivot_wider(names_from = agreement, values_from = n) |>
   mutate(agr = Agree + 0.5*Neutral) |>
   select(var, agr) |>
   mutate(sum = 110) |> 
   ungroup() |> 
   mutate(agr = as.integer(agr), 
          sum = as.integer(sum)) |>
   pcit() |> 
   compare_proportions() |> 
   mutate_round(digits = 2) |>
   filter(adj_p_value < 0.05)
 
 
 bg |>
   select(26:29) |>  
   rowwise()  |> 
   mutate(diff = {
     sorted_values <- sort(c_across(everything()), decreasing = TRUE)
     sorted_values[1] - sorted_values[2]
   }) %>%
   ungroup() |> 
   mutate(row = row_number()) |>
   pivot_longer(cols = 1:4, names_to = "var", values_to = "value") |>
   slice_max(by = row, value, n = 2) |>
   group_by(row) |> 
   mutate(alternatives = paste0(var, collapse = " vs. ")) |>
   ungroup() |> 
   count(diff, alternatives) |> 
   separate(alternatives, into = paste0("alt_", 1:4), sep = " vs. ", fill = "right") |>
   group_by(alt_1) |> 
   summarise(
     n = sum(n),
     sum = sum(diff),
     distance = sum(diff)/n) |> 
   mutate(
     adr = ifelse(distance > 0.264, TRUE, FALSE)) |> 
   ggplot(aes(distance,fct_reorder(alt_1,distance), fill = adr)) +
   geom_col(color = "black")+
   geom_text(
     aes(label = paste0("  ", sprintf(
       "%2.1f", distance * 100
     ), "%  ")),
     #color = agreement > .05
     #hjust = agreement > .05),
     hjust = "right",
     size = 6,
     fontface = "bold",
     family = "Roboto Condensed",
   ) +
   scale_fill_manual(values = monochromeR::generate_palette("#37B7C3", 
                                                            modification = "go_both_ways", 
                                                            n_colours = 2))+
   geom_vline(
     xintercept = 0.264,
     lty = 2,
     size = 0.5,
     color = "#013440"
   ) +
   scale_x_continuous(
     expand = c(0, 0),
     limits = c(-0.05, 0.45),
     breaks = c(seq(0, 1, 0.1)),
     labels = scales::label_percent()
   ) +
   scale_y_discrete(
     labels = c(
       "newmed_balanced" = "Балансирана (QALY & PFS)",
       "newmed_conservative" = "Консервативна (YLG)",
       "newmed_liberal" = "Либерална (Пациентски критерии)",
       "newmed_status_quo" = "Статукво"))+
   guides(
     x = guide_axis(cap = "both"), # Cap both ends
     y = guide_axis(cap = "both") # Cap the upper end
   ) +
   theme(legend.position = "none",
         axis.line = element_line(),
         axis.text = element_text(
           family = "Sofia Sans Condensed", 
           size = 20)) +
   labs(y = "", x = "% Дистанциране")
 
#  ggsave(
#    "med-distance-bg.png",
#    units = "mm",
#    bg = "white",
#    width = 240,
#    height = 120,
#    dpi = 1000
#  )
 
 bg |>
   select(26:29) |>  
   rowwise() %>%
   mutate(diff = {
     sorted_values <- sort(c_across(everything()), decreasing = TRUE)
     sorted_values[1] - sorted_values[2]
   }) %>%
   ungroup() |> 
   mutate(row = row_number()) |>
   pivot_longer(cols = 1:4, names_to = "var", values_to = "value") |>
   slice_max(by = row, value, n = 2) |>
   group_by(row) |> 
   mutate(alternatives = paste0(var, collapse = " vs. ")) |>
   ungroup() |> 
   count(diff, alternatives) |> 
   separate(alternatives, into = paste0("alt_", 1:4), sep = " vs. ", fill = "right") |>
   group_by(alt_1) |>
   summarise(
     n = sum(n),
     sum = sum(diff)) |> 
   select(alt_1, distn = sum, sumn = n) |> 
   mutate(distn = as.integer(distn), 
          sumn = as.integer(sumn)) |>
   pcit() |>
   compare_proportions() |> 
   mutate_round() |> 
   knitr::kable()
 
 
 
 bg |> 
   select(16,17, 26:29) |> 
   correlation::correlation(
     select = c("awareness_interest","power"), 
     select2 = c("newmed_conservative",
                 "newmed_balanced",
                 "newmed_liberal",
                 "newmed_status_quo"), 
     method = "pearson") |>
   tibble() |> 
   filter(p < 0.05) 

 bg |> 
   select(awareness_interest, newmed_liberal) |>
   count(awareness_interest, newmed_liberal) |>
   full_join(expand.grid(awareness_interest = 1:5, newmed_liberal = 1:5)) |>
   mutate(n = ifelse(is.na(n), 0, n),
          sum = sum(n),
          prop = n / sum) |>
   mutate(prop = ifelse(prop < 0.03, 0, prop)) |> 
   ggplot(aes(x = awareness_interest, y = newmed_liberal)) +
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
     awareness_interest = c(1, 2, 3, 4, 5),
     newmed_liberal = c(1, 2, 3, 4, 5)
   ), ) +
   scale_fill_gradient2(
     midpoint = 0.10,
     low = "white",
     mid = "#31B1C2",
     high = "#021526"
   ) +
   theme(legend.position = "none") +
   labs(x = "Самооценка информираност", y = "Либерална алтернатива") 

 #  ggsave(
 #    "cor-med-inform-bg.png",
 #    units = "mm",
 #    bg = "white",
 #    width = 240,
 #    height = 120,
 #    dpi = 1000
 #  )
 
 bg |> 
   select(1,5:17,26:29) |> 
   mutate(
     stateholder = case_when(
       institution_1 == "Академия" ~ "Non-governmental",
       institution_1 == "Законодателна" ~ "Governmental",
       institution_1 == "Изпълнителна" ~ "Governmental",
       institution_1 == "Индустрия" ~ "Non-governmental",
       institution_1 == "Научни дружества" ~ "Non-governmental",
       institution_1 == "Пациентски организации" ~ "Non-governmental",
       institution_1 == "Съсловни организации" ~ "Non-governmental"
     )) |>
   pivot_longer(15:18, names_to = "var", values_to = "value") |>
   filter(var == "newmed_status_quo") |>
   mutate(
     value = as.factor(value)) |>
   select(-c(institution_1, var)) |>
   ordinal::clm(value ~ ., data = _) |> 
   tidy(exp = TRUE, conf.int = TRUE)
 

 
 bg |> 
   select(1,5:17,26:29) |> 
   mutate(
     stateholder = case_when(
       institution_1 == "Академия" ~ "Non-governmental",
       institution_1 == "Законодателна" ~ "Governmental",
       institution_1 == "Изпълнителна" ~ "Governmental",
       institution_1 == "Индустрия" ~ "Non-governmental",
       institution_1 == "Научни дружества" ~ "Non-governmental",
       institution_1 == "Пациентски организации" ~ "Non-governmental",
       institution_1 == "Съсловни организации" ~ "Non-governmental"
     )) |>
   pivot_longer(15:18, names_to = "var", values_to = "value") |>
   filter(var == "newmed_status_quo") |>
   mutate(
     value = as.factor(value)) |>
   select(-c(institution_1, var)) |>
   collect_ordinal_logistic_results(outcome = "value")
 
 bg |>
   select(1,5:17,26:29) |> 
   mutate(
     goverment_sh = case_when(
       institution_1 == "Академия" ~ 0,
       institution_1 == "Законодателна" ~ 1,
       institution_1 == "Изпълнителна" ~ 1,
       institution_1 == "Индустрия" ~ 0,
       institution_1 == "Научни дружества" ~ 0,
       institution_1 == "Пациентски организации" ~ 0,
       institution_1 == "Съсловни организации" ~ 0
     )
   ) |>
   pivot_longer(15:18, names_to = "var", values_to = "value") |>
   mutate(value = as.factor(value)) |>
   mutate(goverment_sh = as.factor(goverment_sh)) |>
   select(-institution_1) |>
   group_by(var) |>
   nest() |>
   mutate(model = map(
     data,
     ~ .x |>
       ordinal::clm(value ~ ., data = _) |>
       tidy(exp = TRUE, conf.int = TRUE)
   )) |>
   unnest(model) |>
   filter(coef.type != "intercept") |>
   select(-c(data, coef.type)) |>
   filter(p.value < 0.05) |>
   mutate(
     CI = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
   ) |> 
   mutate_round(digits = 2) |> 
   knitr::kable()
 
 bg |>
   select(1,5:17,26:29) |> 
   to_dummmy() |> 
   pivot_longer(14:17, names_to = "var", values_to = "value") |>
   mutate(value = as.factor(value)) |> 
   group_by(var) |>
   nest() |>
   mutate(model = map(
     data,
     ~ .x |>
       collect_ordinal_logistic_results(outcome = "value")))|>
   unnest(model) |>
   select(-data) |> 
   filter(!is.na(conf.low)) |>
   mutate(
     CI = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
   ) |> 
   filter(p.value < 0.05) |>
   mutate_round(digits = 2) |> 
   select(-term) |> 
   knitr::kable()

 
 set.seed(123)

# stateholders_med <- 
#   bg |>
#   select(1,5:15,26:29) |>
#   rsample::bootstraps(4000) |>
#   mutate(
#     prop = map(splits, ~ analysis(.x) |>
#                  pivot_longer(cols = 13:16, 
#                               names_to = "var", 
#                               values_to = "value") |>
#                  mutate(
#                    agrm = case_when(
#                      value == 1 ~ "Disagree",
#                      value == 2 ~ "Disagree",
#                      value == 3 ~ "Neutral",
#                      value == 4 ~ "Agree",
#                      value == 5 ~ "Agree")) |>
#                  count(institution_1 ,var,agrm) |> 
#                  pivot_wider(names_from = agrm, values_from = n) |>
#                  mutate_all(~replace_na(., 0)) |>
#                  mutate(agr = Agree + 0.5*Neutral, 
#                         sum = Agree + Disagree + Neutral,
#                         prop = agr/sum) |>
#                  select(-c(Disagree, Neutral, agr, sum, Agree)))) 
 
 
#   stateholders_med |> 
#    unnest(prop) |> 
#    ggplot(aes(prop, 
#               fct_reorder(institution_1, prop))) +
#    stat_halfeye(aes(fill_ramp = after_stat(x > .5)), 
#                 normalize = "groups", 
#                 subguide = "none",
#                 scale = 0.65,
#                 fill = "#211C6A") +
#    geom_vline(xintercept = 0.5, 
#               linewidth = 0.5,
#               linetype = 2,
#               color = "gray10") +
#    scale_fill_ramp_discrete(from = "gray90", guide = "none") +
#    scale_x_continuous(expand = c(0, 0),
#                       limits = c(-0.1, 1.10), 
#                       labels = scales::label_percent(),
#                       breaks = c(seq(-1, 1, 0.2))) +
#    guides(
#      x = guide_axis(cap = "both"), # Cap both ends
#      y = guide_axis(cap = "both") # Cap the upper end
#    ) +
#    theme(legend.position = "none", 
#          axis.line = element_line())+
#    facet_wrap(~var, 
#               labeller = labeller(var = c(
#                 "newmed_balanced" = "Балансирана (QALY & PFS)",
#                 "newmed_conservative" = "Консервативна (YLG)",
#                 "newmed_liberal" = "Либерална (Пациентски критерии)",
#                 "newmed_status_quo" = "Статукво")))+
#    labs(x = "Разпределение на индекса на съгласие", y = "")

#  ggsave(
#    "med-stateholders-bg.png",
#    units = "mm",
#    bg = "white",
#    width = 260,
#    height = 280,
#    dpi = 1000
#  )
 
#  stateholders_med |> 
#    unnest(prop) |>
#    group_by(var, institution_1) |>
#    summarise(
#      mean = median(prop),
#      LCI = quantile(prop, 0.025), 
#      UCI = quantile(prop, 0.975)) |> 
#    mutate(CI = paste0(round(LCI, 2), ", ", round(UCI, 2))) |>
#    select(-c(LCI, UCI)) |>
#    mutate_round(digits = 2) |>
#    knitr::kable() 

 
######---Funding---######
 
 
 bg |> 
   select(30:33) |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |>
   count(var, value) |>
   group_by(var) |>
   mutate(sum = sum(n), 
          prop = (n / sum)) |>
   mutate(value = factor(value)) |> 
   ggplot(aes(x = prop, y = var, fill = value)) +
   geom_col(
     alpha = 0.7,
     position = position_likert()) +
   annotate("rect", 
            xmin=c(0, 0, 0, 0),
            xmax = c(0.63, 0.3, 0.7, 0.3),
            ymin = c(0.5, 1.5, 2.5, 3.5),
            ymax = c(1.5, 2.5, 3.5, 4.5),
            color = "black",
            size = 0.3,
            lty = 2,
            fill = "#BDE8CA",
            alpha = 0.3) +
   geom_text(
     aes(label =ifelse(prop > 0.15, 
                       scales::percent(prop),
                       "")),
     position = position_likert(vjust = 0.5),
     size = 6,
     fontface = "bold",
     angle = 0,
     family = "Sofia Sans Condensed",
   ) +
   geom_text(
     aes(label =ifelse(prop <= 0.15, 
                       scales::percent(prop),
                       "")),
     position = position_likert(vjust = 0.5),
     size = 6,
     fontface = "bold",
     angle = 90,
     family = "Sofia Sans Condensed",
   )+
   geom_vline(xintercept = 0, 
              linetype = 2,
              size = 0.2,
              color = "gray80") +
   scale_fill_manual(values = c("3" = "gray90", 
                                "1" = "#C7253E",
                                "2" = "#E85C0D",
                                "4" = "#41B3A2",
                                "5" = "#0D7C66"))+
   scale_x_continuous(
     label = label_percent_abs(),
     limits = c(-0.85, 0.85),
     breaks = seq(-.8, .8, by = 0.2))+
   scale_y_discrete(
     labels = c(
      "funding_balanced" = "Балансирана (НЗОК лимит и МЗ при нужда)",
      "funding_conservative" = "Консервативна (НЗОК лимит)",   
      "funding_liberal" = "Либерална (НЗОК и МЗ без лимит)",       
      "funding_status_quo" = "Статукво"))+     
   guides(
     x = guide_axis(cap = "both"), # Cap both ends
     y = guide_axis(cap = "both") # Cap the upper end
   ) +
   annotate("text",
            x = c(0.8, 0.8, 0.8, 0.8),
            y = c(1, 2, 3, 4),
            label = c("62.3%", "29.1%", "69.6%", "29.1%") ,
            color = "darkgreen",
            size=7, 
            angle = 0,
            family = "Sofia Sans Condensed")+
   theme(axis.line = element_line(), 
         axis.text = element_text(family = "Sofia Sans Condensed", size = 24),
         legend.position = "none")+
   labs(
     x = "",
     y = ""
   )
 
 
   ggsave(
     "funding-bg.png",
     units = "mm",
     bg = "white",
     width = 340,
     height = 160,
     dpi = 1000
   )
 
 
 bg |> 
   select(30:33) |>  
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   group_by(var) |>
   get_summary_stats() |>
   ggplot(aes(x = mean, y = fct_reorder(var, mean))) +
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
     xintercept = 2.9,
     lty = 2,
     size = 0.5,
     color = "gray10"
   ) +
   scale_y_discrete(
     labels = c(
       "funding_balanced" = "Балансирана (НЗОК лимит и МЗ при нужда)",
       "funding_conservative" = "Консервативна (НЗОК лимит)",   
       "funding_liberal" = "Либерална (НЗОК и МЗ без лимит)",       
       "funding_status_quo" = "Статукво"))+     
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
 
 
#   ggsave(
#     "funding-mean-bg.png",
#     units = "mm",
#     bg = "white",
#     width = 300,
#     height = 120,
#     dpi = 1000
#   )
 
 bg |> 
   select(30:33) |> 
   correlation(redundant = TRUE) |>
   tibble() |>
   mutate(
     Parameter1 = case_when(
       Parameter1 == "funding_balanced" ~ "Балансирана (НЗОК лимит и МЗ при нужда)",
       Parameter1 == "funding_conservative" ~ "Консервативна (НЗОК лимит)",   
       Parameter1 == "funding_liberal" ~  "Либерална (НЗОК и МЗ без лимит)",  
       Parameter1 == "funding_status_quo" ~ "Статукво"
     ),
     Parameter2 = case_when(
       Parameter2 == "funding_balanced" ~ "Балансирана (НЗОК лимит и МЗ при нужда)",
       Parameter2 == "funding_conservative" ~ "Консервативна (НЗОК лимит)",   
       Parameter2 == "funding_liberal" ~ "Либерална (НЗОК и МЗ без лимит)",       
       Parameter2 == "funding_status_quo" ~"Статукво"),
     p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ ""))|>
   filter(Parameter1 != Parameter2) |>
   filter(Parameter1 > Parameter2) |>
   ggplot(aes(Parameter1, Parameter2, fill = r)) +
   geom_tile(color = "gray10") +
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
             fontface = "bold",
             size = 8) +
   theme() +
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
 #   "funding-full-corr-bg.png",
 #   units = "mm",
 #   bg = "white",
 #   width = 380,
 #   height = 160,
 #   dpi = 1000
 # )
 
 bg |> 
   select(30:33) |> 
   correlation(redundant = TRUE) |>
   tibble() |>
   mutate(
     Parameter1 = case_when(
       Parameter1 == "funding_balanced" ~ "Балансирана (НЗОК лимит и МЗ при нужда)",
       Parameter1 == "funding_conservative" ~ "Консервативна (НЗОК лимит)",   
       Parameter1 == "funding_liberal" ~  "Либерална (НЗОК и МЗ без лимит)",  
       Parameter1 == "funding_status_quo" ~ "Статукво"
     ),
     Parameter2 = case_when(
       Parameter2 == "funding_balanced" ~ "Балансирана (НЗОК лимит и МЗ при нужда)",
       Parameter2 == "funding_conservative" ~ "Консервативна (НЗОК лимит)",   
       Parameter2 == "funding_liberal" ~ "Либерална (НЗОК и МЗ без лимит)",       
       Parameter2 == "funding_status_quo" ~"Статукво"),
     p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ ""))|>
   filter(Parameter1 != Parameter2) |>
   filter(Parameter1 > Parameter2) |>
   mutate_round() |> 
   filter(p<0.05) |>
   select(-Method) |>
   knitr::kable()
 
 
 bg |> 
   select(30:33) |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   group_by(var) |>
   get_summary_stats() |> 
   mutate(
     LCI = mean - ci, 
     UCI = mean + ci) |>
   select(var, mean, LCI, UCI)
 
 
 bg |> 
   select(30:33) |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   aov(value ~ var, data = _) |>
   emmeans::emmeans(pairwise ~ "var", 
                    mode = "eff.size", 
                    adjust = "bonferroni") 
 
 bg |> 
   select(30:33)  |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   mutate(agreement =
            case_when(
              value == 1 ~ "Disagree",
              value == 2 ~ "Disagree",
              value == 3 ~ "Neutral",
              value == 4 ~ "Agree",
              value == 5 ~ "Agree")) |> 
   count(var, agreement) |>
   pivot_wider(names_from = agreement, values_from = n) |>
   mutate(agr = Agree + 0.5*Neutral) |>
   select(var, agr) |>
   mutate(sum = 110) |> 
   ungroup() |> 
   mutate(agr = as.integer(agr), 
          sum = as.integer(sum)) |> 
   select(var, agr) |>
   pivot_wider(names_from = var, values_from = agr) |>
   rstatix::chisq_test() 
 
 
 bg |> 
   select(30:33) |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   mutate(agreement =
            case_when(
              value == 1 ~ "Disagree",
              value == 2 ~ "Disagree",
              value == 3 ~ "Neutral",
              value == 4 ~ "Agree",
              value == 5 ~ "Agree")) |> 
   count(var, agreement) |>
   pivot_wider(names_from = agreement, values_from = n) |>
   mutate(agr = Agree + 0.5*Neutral) |>
   select(var, agr) |>
   mutate(sum = 110) |> 
   ungroup() |> 
   mutate(agr = as.integer(agr), 
          sum = as.integer(sum)) |>
   pcit() |> 
   compare_proportions() |> 
   mutate_round(digits = 2) |>
   filter(adj_p_value < 0.05)
 
 
 bg |>
   select(30:33) |>  
   rowwise()  |> 
   mutate(diff = {
     sorted_values <- sort(c_across(everything()), decreasing = TRUE)
     sorted_values[1] - sorted_values[2]
   }) %>%
   ungroup() |> 
   mutate(row = row_number()) |>
   pivot_longer(cols = 1:4, names_to = "var", values_to = "value") |>
   slice_max(by = row, value, n = 2) |>
   group_by(row) |> 
   mutate(alternatives = paste0(var, collapse = " vs. ")) |>
   ungroup() |> 
   count(diff, alternatives) |> 
   separate(alternatives, into = paste0("alt_", 1:4), sep = " vs. ", fill = "right") |>
   group_by(alt_1) |> 
   summarise(
     n = sum(n),
     sum = sum(diff),
     distance = sum(diff)/n) |> 
   mutate(
     adr = ifelse(distance > 0.286, TRUE, FALSE)) |> 
   ggplot(aes(distance,fct_reorder(alt_1,distance), fill = adr)) +
   geom_col(color = "black")+
   geom_text(
     aes(label = paste0("  ", sprintf(
       "%2.1f", distance * 100
     ), "%  ")),
     #color = agreement > .05
     #hjust = agreement > .05),
     hjust = "right",
     size = 6,
     fontface = "bold",
     family = "Roboto Condensed",
   ) +
   scale_fill_manual(values = monochromeR::generate_palette("#37B7C3", 
                                                            modification = "go_both_ways", 
                                                            n_colours = 2))+
   geom_vline(
     xintercept = 0.286,
     lty = 2,
     size = 0.5,
     color = "#013440"
   ) +
   scale_x_continuous(
     expand = c(0, 0),
     limits = c(-0.05, 0.45),
     breaks = c(seq(0, 1, 0.1)),
     labels = scales::label_percent()
   ) +
   scale_y_discrete(
     labels = c(
       "funding_balanced" = "Балансирана (НЗОК лимит и МЗ при нужда)",
       "funding_conservative" = "Консервативна (НЗОК лимит)",   
       "funding_liberal" = "Либерална (НЗОК и МЗ без лимит)",       
       "funding_status_quo" = "Статукво"))+   
   guides(
     x = guide_axis(cap = "both"), # Cap both ends
     y = guide_axis(cap = "both") # Cap the upper end
   ) +
   theme(legend.position = "none",
         axis.line = element_line(),
         axis.text = element_text(
           family = "Sofia Sans Condensed", 
           size = 20)) +
   labs(y = "", x = "% Дистанциране")
 
#   ggsave(
#     "funding-distance-bg.png",
#     units = "mm",
#     bg = "white",
#     width = 240,
#     height = 120,
#     dpi = 1000
#   )
 
 bg |>
   select(30:33) |>  
   rowwise() %>%
   mutate(diff = {
     sorted_values <- sort(c_across(everything()), decreasing = TRUE)
     sorted_values[1] - sorted_values[2]
   }) %>%
   ungroup() |> 
   mutate(row = row_number()) |>
   pivot_longer(cols = 1:4, names_to = "var", values_to = "value") |>
   slice_max(by = row, value, n = 2) |>
   group_by(row) |> 
   mutate(alternatives = paste0(var, collapse = " vs. ")) |>
   ungroup() |> 
   count(diff, alternatives) |> 
   separate(alternatives, into = paste0("alt_", 1:4), sep = " vs. ", fill = "right") |>
   group_by(alt_1) |>
   summarise(
     n = sum(n),
     sum = sum(diff)) |> 
   select(alt_1, distn = sum, sumn = n) |> 
   mutate(distn = as.integer(distn), 
          sumn = as.integer(sumn)) |>
   pcit() |>
   compare_proportions() |> 
   mutate_round() |> 
   knitr::kable()
 
 
 
 bg |> 
   select(16,17, 30:33) |> 
   correlation::correlation(
     select = c("awareness_interest","power"), 
     select2 = c("funding_conservative",
                 "funding_balanced",
                 "funding_liberal",
                 "funding_status_quo")) |>
   tibble() |> 
   filter(p < 0.05) 
 
# bg |> 
#   select(awareness_interest, newmed_liberal) |>
#   count(awareness_interest, newmed_liberal) |>
#   full_join(expand.grid(awareness_interest = 1:5, newmed_liberal = 1:5)) |>
#   mutate(n = ifelse(is.na(n), 0, n),
#          sum = sum(n),
#          prop = n / sum) |>
#   mutate(prop = ifelse(prop < 0.03, 0, prop)) |> 
#   ggplot(aes(x = awareness_interest, y = newmed_liberal)) +
#   geom_tile(
#     aes(fill = prop),
#     color = "white",
#     alpha = 0.9,
#     linewidth = 1
#   ) +
#   geom_text(
#     aes(label = ifelse(prop > 0,
#                        paste0("  ", sprintf(
#                          "%2.1f", prop * 100
#                        ), "%  "),
#                        ""
#     )),
#     vjust = 0.5,
#     hjust = 0.5,
#     size = 5,
#     family = "Roboto Condensed",
#   ) +
#   geom_rangeframe(data = tibble(
#     awareness_interest = c(1, 2, 3, 4, 5),
#     newmed_liberal = c(1, 2, 3, 4, 5)
#   ), ) +
#   scale_fill_gradient2(
#     midpoint = 0.10,
#     low = "white",
#     mid = "#31B1C2",
#     high = "#021526"
#   ) +
#   theme(legend.position = "none") +
#   labs(x = "Самооценка информираност", y = "Либерална алтернатива") 
 
 #  ggsave(
 #    "cor-med-inform-bg.png",
 #    units = "mm",
 #    bg = "white",
 #    width = 240,
 #    height = 120,
 #    dpi = 1000
 #  )
 
 bg |> 
   select(1,5:17,30:33) |> 
   mutate(
     stateholder = case_when(
       institution_1 == "Академия" ~ "Non-governmental",
       institution_1 == "Законодателна" ~ "Governmental",
       institution_1 == "Изпълнителна" ~ "Governmental",
       institution_1 == "Индустрия" ~ "Non-governmental",
       institution_1 == "Научни дружества" ~ "Non-governmental",
       institution_1 == "Пациентски организации" ~ "Non-governmental",
       institution_1 == "Съсловни организации" ~ "Non-governmental"
     )) |>
   pivot_longer(15:18, names_to = "var", values_to = "value") |>
   filter(var == "funding_status_quo") |>
   mutate(
     value = as.factor(value)) |>
   select(-c(institution_1, var)) |>
   ordinal::clm(value ~ ., data = _) |> 
   tidy(exp = TRUE, conf.int = TRUE)
 
 
 bg |>
   select(1,5:17,30:33) |> 
   mutate(
     goverment_sh = case_when(
       institution_1 == "Академия" ~ 0,
       institution_1 == "Законодателна" ~ 1,
       institution_1 == "Изпълнителна" ~ 1,
       institution_1 == "Индустрия" ~ 0,
       institution_1 == "Научни дружества" ~ 0,
       institution_1 == "Пациентски организации" ~ 0,
       institution_1 == "Съсловни организации" ~ 0
     )
   ) |>
   pivot_longer(15:18, names_to = "var", values_to = "value") |>
   mutate(value = as.factor(value)) |>
   mutate(goverment_sh = as.factor(goverment_sh)) |>
   select(-institution_1) |>
   group_by(var) |>
   nest() |>
   mutate(model = map(
     data,
     ~ .x |>
       ordinal::clm(value ~ ., data = _) |>
       tidy(exp = TRUE, conf.int = TRUE)
   )) |>
   unnest(model) |>
   filter(coef.type != "intercept") |>
   select(-c(data, coef.type)) |>
   filter(p.value < 0.05) |>
   mutate(
     CI = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
   ) |> 
   mutate_round(digits = 2) |> 
   knitr::kable()
 
 bg |>
   select(1,5:17,30:33) |> 
   to_dummmy() |> 
   pivot_longer(14:17, names_to = "var", values_to = "value") |>
   mutate(value = as.factor(value)) |> 
   group_by(var) |>
   nest() |>
   mutate(model = map(
     data,
     ~ .x |>
       collect_ordinal_logistic_results(outcome = "value")))|>
   unnest(model) |>
   select(-data) |> 
   filter(!is.na(conf.low)) |>
   mutate(
     CI = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
   ) |> 
   filter(p.value < 0.05) |>
   mutate_round(digits = 2) |> 
   select(-term) |> 
   knitr::kable()
 
 # set.seed(123)
 # 
 # stateholders_funding <- 
 #   bg |>
 #   select(1,5:15,30:33) |>
 #   pivot_longer(cols = 13:16, 
 #                names_to = "var", 
 #                values_to = "value") |>
 #   mutate(
 #     agrm = case_when(
 #       value == 1 ~ "Disagree",
 #       value == 2 ~ "Disagree",
 #       value == 3 ~ "Neutral",
 #       value == 4 ~ "Agree",
 #       value == 5 ~ "Agree")) |>
 #   rsample::bootstraps(4000) |>
 #   mutate(
 #       prop = map(splits, ~ analysis(.x) |>
 #                    count(institution_1 ,var,agrm) |> 
 #                    pivot_wider(names_from = agrm, values_from = n) |>
 #                    mutate_all(~replace_na(., 0)) |>
 #                    mutate(agr = Agree + 0.5*Neutral, 
 #                           sum = Agree + Disagree + Neutral,
 #                           prop = agr/sum) |>
 #                    select(-c(Disagree, Neutral, agr, sum, Agree))))
 
 
 # stateholders_funding |> 
 #    unnest(prop) |> 
 #    ggplot(aes(prop, 
 #               fct_reorder(institution_1, prop))) +
 #    stat_halfeye(aes(fill_ramp = after_stat(x > .5)), 
 #                 normalize = "xy", 
 #                 subguide = "none",
 #                 scale = 0.75,
 #                 fill = "#211C6A") +
 #    geom_vline(xintercept = 0.5, 
 #               linewidth = 0.5,
 #               linetype = 2,
 #               color = "gray10") +
 #    scale_fill_ramp_discrete(from = "gray90", guide = "none") +
 #    scale_x_continuous(expand = c(0, 0),
 #                       limits = c(-0.1, 1.10), 
 #                       labels = scales::label_percent(),
 #                       breaks = c(seq(-1, 1, 0.2))) +
 #    guides(
 #      x = guide_axis(cap = "both"), # Cap both ends
 #      y = guide_axis(cap = "both") # Cap the upper end
 #    ) +
 #    theme(legend.position = "none", 
 #          axis.line = element_line())+
 #    facet_wrap(~var, 
 #               labeller = labeller(var = c(
 #                 "funding_balanced" = "Балансирана (НЗОК лимит и МЗ при нужда)",
 #                 "funding_conservative" = "Консервативна (НЗОК лимит)",   
 #                 "funding_liberal" = "Либерална (НЗОК и МЗ без лимит)",       
 #                 "funding_status_quo" = "Статукво")))+   
 #    labs(x = "Разпределение на индекса на съгласие", y = "")
 
 #  ggsave(
 #    "funding-stateholders-bg.png",
 #    units = "mm",
 #    bg = "white",
 #    width = 260,
 #    height = 280,
 #    dpi = 1000
 #  )
 
# stateholders_funding |> 
#   unnest(prop) |>
#   group_by(var, institution_1) |>
#   summarise(
#     mean = median(prop),
#     LCI = quantile(prop, 0.025), 
#     UCI = quantile(prop, 0.975)) |> 
#   mutate(CI = paste0(round(LCI, 2), ", ", round(UCI, 2))) |>
#   select(-c(LCI, UCI)) |>
#   mutate_round(digits = 2) |>
#   knitr::kable() 
 

######---Registry---######
 
 bg |> 
   select(34:37) |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |>
   count(var, value) |>
   group_by(var) |>
   mutate(sum = sum(n), 
          prop = (n / sum)) |>
   mutate(value = factor(value)) |> 
   ggplot(aes(x = prop, y = var, fill = value)) +
   geom_col(
     alpha = 0.7,
     position = position_likert()) +
   annotate("rect", 
            xmin=c(0, 0, 0, 0),
            xmax = c(0.81, 0.46, 0.5, 0.13),
            ymin = c(0.5, 1.5, 2.5, 3.5),
            ymax = c(1.5, 2.5, 3.5, 4.5),
            color = "black",
            size = 0.3,
            lty = 2,
            fill = "#BDE8CA",
            alpha = 0.3) +
   geom_text(
     aes(label =ifelse(prop > 0.15, 
                       scales::percent(prop),
                       "")),
     position = position_likert(vjust = 0.5),
     size = 6,
     fontface = "bold",
     angle = 0,
     family = "Sofia Sans Condensed",
   ) +
   geom_text(
     aes(label =ifelse(prop <= 0.15, 
                       scales::percent(prop),
                       "")),
     position = position_likert(vjust = 0.5),
     size = 6,
     fontface = "bold",
     angle = 90,
     family = "Sofia Sans Condensed",
   )+
   geom_vline(xintercept = 0, 
              linetype = 2,
              size = 0.2,
              color = "gray80") +
   scale_fill_manual(values = c("3" = "gray90", 
                                "1" = "#C7253E",
                                "2" = "#E85C0D",
                                "4" = "#41B3A2",
                                "5" = "#0D7C66"))+
   scale_x_continuous(
     label = label_percent_abs(),
     limits = c(-0.9, 0.9),
     breaks = seq(-.9, .9, by = 0.3))+
   scale_y_discrete(
     labels = c(
      "reg_balanced" = "Балансирана \n(Общ НРР с допълнителни полета)",     
      "reg_conservative" = "Консервативна \n(Общ НРР без допълнителни полета)", 
      "reg_liberal" = "Либерална \n(Отделен регистър)",        
      "reg_status_quo" = "Статукво"))+        
   guides(
     x = guide_axis(cap = "both"), # Cap both ends
     y = guide_axis(cap = "both") # Cap the upper end
   ) +
   annotate("text",
            x = c(0.9, 0.9, 0.9, 0.9),
            y = c(1, 2, 3, 4),
            label = c("80.4%", "45.5%", "49.1%", "12.3%") ,
            color = "darkgreen",
            size=7, 
            angle = 0,
            family = "Sofia Sans Condensed")+
   theme(axis.line = element_line(), 
         axis.text = element_text(family = "Sofia Sans Condensed", size = 26),
         legend.position = "none")+
   labs(
     x = "",
     y = ""
   )
 
ggsave(
  "reg-bg.png",
  units = "mm",
  bg = "white",
  width = 500,
  height = 220,
  dpi = 1000
)
 
 
 bg |> 
   select(34:37) |>  
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   group_by(var) |>
   get_summary_stats() |>
   ggplot(aes(x = mean, y = fct_reorder(var, mean))) +
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
     xintercept = 2.92,
     lty = 2,
     size = 0.5,
     color = "gray10"
   ) +
   scale_y_discrete(
     labels = c(
       "reg_balanced" = "Балансирана (Общ НРР с допълнителни полета)",     
       "reg_conservative" = "Консервативна (Общ НРР без допълнителни полета)", 
       "reg_liberal" = "Либерална (Отделен регистър)",        
       "reg_status_quo" = "Статукво"))+      
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
 
 
 #   ggsave(
 #     "reg-mean-bg.png",
 #     units = "mm",
 #     bg = "white",
 #     width = 300,
 #     height = 120,
 #     dpi = 1000
 #   )
 
 bg |> 
   select(34:37) |> 
   correlation(redundant = TRUE) |>
   tibble() |>
   mutate(
     Parameter1 = case_when(
       Parameter1 == "reg_balanced" ~ "Балансирана \n(Общ НРР с допълнителни полета)",   
       Parameter1 == "reg_conservative" ~  "Консервативна \n(Общ НРР без допълнителни полета)",
       Parameter1 == "reg_liberal" ~ "Либерална \n(Отделен регистър)",        
       Parameter1 == "reg_status_quo" ~ "Статукво"
     ),
     Parameter2 = case_when(
       Parameter2 == "reg_balanced" ~ "Балансирана \n(Общ НРР с допълнителни полета)",   
       Parameter2 == "reg_conservative" ~ "Консервативна \n(Общ НРР без допълнителни полета)",
       Parameter2 == "reg_liberal" ~ "Либерална \n(Отделен регистър)",          
       Parameter2 == "reg_status_quo" ~"Статукво"),
     p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ ""))|>
   filter(Parameter1 != Parameter2) |>
   filter(Parameter1 > Parameter2) |>
   ggplot(aes(Parameter1, Parameter2, fill = r)) +
   geom_tile(color = "gray10") +
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
             fontface = "bold",
             size = 8) +
   theme() +
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
#   "reg-full-corr-bg.png",
#   units = "mm",
#   bg = "white",
#   width = 360,
#   height = 140,
#   dpi = 1000
# )
 
 bg |> 
   select(34:37) |> 
   correlation(redundant = TRUE) |>
   tibble() |>
   mutate(
     Parameter1 = case_when(
       Parameter1 == "reg_balanced" ~ "Балансирана \n(Общ НРР с допълнителни полета)",   
       Parameter1 == "reg_conservative" ~  "Консервативна \n(Общ НРР без допълнителни полета)",
       Parameter1 == "reg_liberal" ~ "Либерална \n(Отделен регистър)",        
       Parameter1 == "reg_status_quo" ~ "Статукво"
     ),
     Parameter2 = case_when(
       Parameter2 == "reg_balanced" ~ "Балансирана \n(Общ НРР с допълнителни полета)",   
       Parameter2 == "reg_conservative" ~ "Консервативна \n(Общ НРР без допълнителни полета)",
       Parameter2 == "reg_liberal" ~ "Либерална \n(Отделен регистър)",          
       Parameter2 == "reg_status_quo" ~"Статукво"),
     p_astr = case_when(p < 0.001 ~ "***", p < 0.01 ~ "**", p < 0.05 ~ "*", TRUE ~ ""))|>
   filter(Parameter1 != Parameter2) |>
   filter(Parameter1 > Parameter2) |>
 mutate_round() |> 
   filter(p<0.05) |>
   select(-Method) |>
   knitr::kable()
 
 bg |> 
   select(34:37) |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   group_by(var) |>
   get_summary_stats() |> 
   mutate(
     LCI = mean - ci, 
     UCI = mean + ci) |>
   select(var, mean, LCI, UCI)
 
 
 bg |> 
   select(34:37)  |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   aov(value ~ var, data = _) |>
   emmeans::emmeans(pairwise ~ "var", 
                    mode = "eff.size", 
                    adjust = "bonferroni") 
 
 bg |> 
   select(34:37)  |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   mutate(agreement =
            case_when(
              value == 1 ~ "Disagree",
              value == 2 ~ "Disagree",
              value == 3 ~ "Neutral",
              value == 4 ~ "Agree",
              value == 5 ~ "Agree")) |> 
   count(var, agreement) |>
   pivot_wider(names_from = agreement, values_from = n) |>
   mutate(agr = Agree + 0.5*Neutral) |>
   select(var, agr) |>
   mutate(sum = 110) |> 
   ungroup() |> 
   mutate(agr = as.integer(agr), 
          sum = as.integer(sum)) |> 
   select(var, agr) |>
   pivot_wider(names_from = var, values_from = agr) |>
   rstatix::chisq_test() 
 
 
 bg |> 
   select(34:37)  |> 
   pivot_longer(cols = everything(), names_to = "var", values_to = "value") |> 
   mutate(agreement =
            case_when(
              value == 1 ~ "Disagree",
              value == 2 ~ "Disagree",
              value == 3 ~ "Neutral",
              value == 4 ~ "Agree",
              value == 5 ~ "Agree")) |> 
   count(var, agreement) |>
   pivot_wider(names_from = agreement, values_from = n) |>
   mutate(agr = Agree + 0.5*Neutral) |>
   select(var, agr) |>
   mutate(sum = 110) |> 
   ungroup() |> 
   mutate(agr = as.integer(agr), 
          sum = as.integer(sum)) |>
   pcit() |> 
   compare_proportions() |> 
   mutate_round(digits = 2) |>
   filter(adj_p_value < 0.05)
 
 
 bg |>
   select(34:37) |>  
   rowwise()  |> 
   mutate(diff = {
     sorted_values <- sort(c_across(everything()), decreasing = TRUE)
     sorted_values[1] - sorted_values[2]
   }) %>%
   ungroup() |> 
   mutate(row = row_number()) |>
   pivot_longer(cols = 1:4, names_to = "var", values_to = "value") |>
   slice_max(by = row, value, n = 2) |>
   group_by(row) |> 
   mutate(alternatives = paste0(var, collapse = " vs. ")) |>
   ungroup() |> 
   count(diff, alternatives) |> 
   separate(alternatives, into = paste0("alt_", 1:4), sep = " vs. ", fill = "right") |>
   group_by(alt_1) |> 
   summarise(
     n = sum(n),
     sum = sum(diff),
     distance = sum(diff)/n) |> 
   mutate(
     adr = ifelse(distance > 0.338, TRUE, FALSE)) |> 
   ggplot(aes(distance,fct_reorder(alt_1,distance), fill = adr)) +
   geom_col(color = "black")+
   geom_text(
     aes(label = paste0("  ", sprintf(
       "%2.1f", distance * 100
     ), "%  ")),
     #color = agreement > .05
     #hjust = agreement > .05),
     hjust = "right",
     size = 6,
     fontface = "bold",
     family = "Roboto Condensed",
   ) +
   scale_fill_manual(values = monochromeR::generate_palette("#37B7C3", 
                                                            modification = "go_both_ways", 
                                                            n_colours = 2))+
   geom_vline(
     xintercept = 0.338,
     lty = 2,
     size = 0.5,
     color = "#013440"
   ) +
   scale_x_continuous(
     expand = c(0, 0),
     limits = c(-0.05, 0.85),
     breaks = c(seq(0, 1, 0.2)),
     labels = scales::label_percent()
   ) +
   scale_y_discrete(
     labels = c(
       "reg_balanced" = "Балансирана \n(Общ НРР с допълнителни полета)",     
       "reg_conservative" = "Консервативна \n(Общ НРР без допълнителни полета)", 
       "reg_liberal" = "Либерална \n(Отделен регистър)",        
       "reg_status_quo" = "Статукво"))+   
   guides(
     x = guide_axis(cap = "both"), # Cap both ends
     y = guide_axis(cap = "both") # Cap the upper end
   ) +
   theme(legend.position = "none",
         axis.line = element_line(),
         axis.text = element_text(
           family = "Sofia Sans Condensed", 
           size = 20)) +
   labs(y = "", x = "% Дистанциране")
 
#    ggsave(
#      "reg-distance-bg.png",
#      units = "mm",
#      bg = "white",
#      width = 240,
#      height = 120,
#      dpi = 1000
#    )
 
 bg |>
   select(34:37)  |>  
   rowwise() %>%
   mutate(diff = {
     sorted_values <- sort(c_across(everything()), decreasing = TRUE)
     sorted_values[1] - sorted_values[2]
   }) %>%
   ungroup() |> 
   mutate(row = row_number()) |>
   pivot_longer(cols = 1:4, names_to = "var", values_to = "value") |>
   slice_max(by = row, value, n = 2) |>
   group_by(row) |> 
   mutate(alternatives = paste0(var, collapse = " vs. ")) |>
   ungroup() |> 
   count(diff, alternatives) |> 
   separate(alternatives, into = paste0("alt_", 1:4), sep = " vs. ", fill = "right") |>
   group_by(alt_1) |>
   summarise(
     n = sum(n),
     sum = sum(diff)) |> 
   select(alt_1, distn = sum, sumn = n) |> 
   mutate(distn = as.integer(distn)) |> 
   select(distn,alt_1) |> 
   pivot_wider(names_from = alt_1, values_from = distn) |>
   rstatix::chisq_test()
 
 bg |>
   select(34:37)  |>  
   rowwise() %>%
   mutate(diff = {
     sorted_values <- sort(c_across(everything()), decreasing = TRUE)
     sorted_values[1] - sorted_values[2]
   }) %>%
   ungroup() |> 
   mutate(row = row_number()) |>
   pivot_longer(cols = 1:4, names_to = "var", values_to = "value") |>
   slice_max(by = row, value, n = 2) |>
   group_by(row) |> 
   mutate(alternatives = paste0(var, collapse = " vs. ")) |>
   ungroup() |> 
   count(diff, alternatives) |> 
   separate(alternatives, into = paste0("alt_", 1:4), sep = " vs. ", fill = "right") |>
   group_by(alt_1) |>
   summarise(
     n = sum(n),
     sum = sum(diff)) |> 
   select(alt_1, distn = sum, sumn = n) |> 
   mutate(distn = as.integer(distn), 
          sumn = as.integer(sumn)) |>
   pcit() |>
   compare_proportions() |> 
   mutate_round() |> 
   filter(adj_p_value < 0.05) |>
   knitr::kable()
 
 
 
 bg |> 
   select(16,17, 34:37) |> 
   correlation::correlation(
     select = c("awareness_interest","power"), 
     select2 = c("reg_conservative",
                 "reg_balanced",
                 "reg_liberal",
                 "reg_status_quo")) |>
   tibble() |> 
   filter(p < 0.05) 
 
  bg |> 
    select(awareness_interest, reg_conservative) |>
    count(awareness_interest, reg_conservative) |>
    full_join(expand.grid(awareness_interest = 1:5, reg_conservative = 1:5)) |>
    mutate(n = ifelse(is.na(n), 0, n),
           sum = sum(n),
           prop = n / sum) |>
    mutate(prop = ifelse(prop < 0.035, 0, prop)) |> 
    ggplot(aes(x = awareness_interest, y = reg_conservative)) +
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
      awareness_interest = c(1, 2, 3, 4, 5),
      reg_conservative = c(1, 2, 3, 4, 5)
    ), ) +
    scale_fill_gradient2(
      midpoint = 0.10,
      low = "white",
      mid = "#31B1C2",
      high = "#021526"
    ) +
    theme(legend.position = "none") +
    labs(x = "Самооценка информираност", y = "Консервативна алтернатива") 
 
#   ggsave(
#     "reg-cor-inform-bg.png",
#     units = "mm",
#     bg = "white",
#     width = 240,
#     height = 120,
#     dpi = 1000
#   )
 
 bg |> 
   select(1,5:17,34:37) |> 
   mutate(
     stateholder = case_when(
       institution_1 == "Академия" ~ "Non-governmental",
       institution_1 == "Законодателна" ~ "Governmental",
       institution_1 == "Изпълнителна" ~ "Governmental",
       institution_1 == "Индустрия" ~ "Non-governmental",
       institution_1 == "Научни дружества" ~ "Non-governmental",
       institution_1 == "Пациентски организации" ~ "Non-governmental",
       institution_1 == "Съсловни организации" ~ "Non-governmental"
     )) |>
   pivot_longer(15:18, names_to = "var", values_to = "value") |>
   filter(var == "reg_status_quo") |>
   mutate(
     value = as.factor(value)) |>
   select(-c(institution_1, var)) |>
   ordinal::clm(value ~ ., data = _) |> 
   tidy(exp = TRUE, conf.int = TRUE)
 
 
 bg |>
   select(1,5:17,34:37) |> 
   mutate(
     goverment_sh = case_when(
       institution_1 == "Академия" ~ 0,
       institution_1 == "Законодателна" ~ 1,
       institution_1 == "Изпълнителна" ~ 1,
       institution_1 == "Индустрия" ~ 0,
       institution_1 == "Научни дружества" ~ 0,
       institution_1 == "Пациентски организации" ~ 0,
       institution_1 == "Съсловни организации" ~ 0
     )
   ) |>
   pivot_longer(15:18, names_to = "var", values_to = "value") |>
   mutate(value = as.factor(value)) |>
   mutate(goverment_sh = as.factor(goverment_sh)) |>
   select(-institution_1) |>
   group_by(var) |>
   nest() |>
   mutate(model = map(
     data,
     ~ .x |>
       ordinal::clm(value ~ ., data = _) |>
       tidy(exp = TRUE, conf.int = TRUE)
   )) |>
   unnest(model) |>
   filter(coef.type != "intercept") |>
   select(-c(data, coef.type)) |>
   filter(p.value < 0.05) |>
   mutate(
     CI = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
   ) |> 
   mutate_round(digits = 2) |> 
   knitr::kable()
 
 bg |>
   select(1,5:17,34:37) |> 
   to_dummmy() |> 
   pivot_longer(14:17, names_to = "var", values_to = "value") |>
   mutate(value = as.factor(value)) |> 
   group_by(var) |>
   nest() |>
   mutate(model = map(
     data,
     ~ .x |>
       collect_ordinal_logistic_results(outcome = "value")))|>
   unnest(model) |>
   select(-data) |> 
   filter(!is.na(conf.low)) |>
   mutate(
     CI = paste0(round(conf.low, 2), ", ", round(conf.high, 2)),
   ) |> 
   filter(p.value < 0.05) |>
   mutate_round(digits = 2) |> 
   select(-term) |> 
   knitr::kable()
 
  set.seed(123)
  
#  stateholders_reg <-
#    bg |>
#    select(1, 5:15, 34:37) |>
#    pivot_longer(cols = 13:16,
#                 names_to = "var",
#                 values_to = "value") |>
#    mutate(
#      agrm = case_when(
#        value == 1 ~ "Disagree",
#        value == 2 ~ "Disagree",
#        value == 3 ~ "Neutral",
#        value == 4 ~ "Agree",
#        value == 5 ~ "Agree"
#      )
#    ) |>
#    rsample::bootstraps(4000) |>
#    mutate(prop = map(
#      splits,
#      ~ analysis(.x) |>
#        count(institution_1 , var, agrm) |>
#        pivot_wider(names_from = agrm, values_from = n) |>
#        mutate_all( ~ replace_na(., 0)) |>
#        mutate(
#          agr = Agree + 0.5 * Neutral,
#          sum = Agree + Disagree + Neutral,
#          prop = agr / sum
#        ) |>
#        select(-c(Disagree, Neutral, agr, sum, Agree))
#    ))

 
#  stateholders_reg |>
#    unnest(prop) |>
#    ggplot(aes(prop, fct_reorder(institution_1, prop))) +
#    stat_halfeye(
#      aes(fill_ramp = after_stat(x > .5)),
#      normalize = "xy",
#      subguide = "none",
#      scale = 0.75,
#      fill = "#211C6A"
#    ) +
#    geom_vline(
#      xintercept = 0.5,
#      linewidth = 0.5,
#      linetype = 2,
#      color = "gray10"
#    ) +
#    scale_fill_ramp_discrete(from = "gray90", guide = "none") +
#    scale_x_continuous(
#      expand = c(0, 0),
#      limits = c(-0.1, 1.10),
#      labels = scales::label_percent(),
#      breaks = c(seq(-1, 1, 0.2))
#    ) +
#    guides(x = guide_axis(cap = "both"), y = guide_axis(cap = "both")) +
#    theme(legend.position = "none", axis.line = element_line()) +
#    facet_wrap( ~ var, labeller = labeller(
#      var = c(
#        "reg_balanced" = "Балансирана \n(Общ НРР с допълнителни полета)",     
#        "reg_conservative" = "Консервативна \n(Общ НРР без допълнителни полета)"#, 
#        "reg_liberal" = "Либерална \n(Отделен регистър)",        
#        "reg_status_quo" = "Статукво")
#      )
#    ) +
#    labs(x = "Разпределение на индекса на съгласие", y = "")
 
#   ggsave(
#     "reg-stateholders-bg.png",
#     units = "mm",
#     bg = "white",
#     width = 260,
#     height = 280,
#     dpi = 1000
#   )

  
#   stateholders_reg |> 
#    unnest(prop) |>
#    group_by(var, institution_1) |>
#    summarise(
#      mean = median(prop),
#      LCI = quantile(prop, 0.025), 
#      UCI = quantile(prop, 0.975)) |> 
#    mutate(CI = paste0(round(LCI, 2), ", ", round(UCI, 2))) |>
#    select(-c(LCI, UCI)) |>
#    mutate_round(digits = 2) |>
#    knitr::kable() 
  
  
######---Clustering---######
  
bg |> 
  mutate(rowid = row_number()) |>
  select(-c(2:4)) |> 
  pivot_longer(cols = 15:34, names_to = "var", values_to = "value") |>
  separate(var, into = c("cluster", "alternative"), sep = "_", extra = "merge", fill = "right")
  
  
combination_top <- 
  bg |>
    mutate(rowid = row_number()) |>
    select(-c(2:4)) |>
    pivot_longer(cols = 15:34,
                 names_to = "var",
                 values_to = "value") |>
    separate(
      var,
      into = c("cluster", "alternative"),
      sep = "_",
      extra = "merge",
      fill = "right"
    ) |>
    group_by(rowid, cluster) |>
    slice_max(value, n = 1) |>
    ungroup() |>
    count(cluster, alternative) |>
    group_by(cluster) |>
    mutate(sum = sum(n)) |>
    slice_max(n, n = 1) |>
    mutate(group = paste0(cluster, "_", alternative)) |>
    ungroup() |>
    select(group, n, sum) |>
    mutate(
      group = case_when(
        group == "def_conservative" ~ "Консервативна дефиниция",
        group == "funding_liberal" ~ "Либерално финансиране",
        group == "newmed_balanced" ~ "Балансирани критерии за реимбурсация",
        group == "organisation_conservative" ~ "Консервативна организация",
        group == "reg_balanced" ~ "Балансиран модел на регистрация"
      )) |> 
    pcit() |>
    ggplot(aes(
      x = proportion,
      y = fct_reorder(group, proportion),
      fill = group
    )) +
    geom_col(width = .5, 
             alpha = 0.6,
             color = "gray10") +
    geom_text(
      aes(label = group, x = 0),
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
      breaks = c(seq(0, .6, 0.2)),
      labels = scales::label_percent()
    ) +
    scale_y_discrete(guide = "none") +
    scale_fill_manual(values = 
                        c("Консервативна дефиниция" = "#C7253E",
                          "Либерално финансиране" = "#E85C0D",
                          "Балансирани критерии за реимбурсация" = "#41B3A2",
                          "Консервативна организация" = "#0D7C66",
                          "Балансиран модел на регистрация" = "#013440")) +
    guides(
      x = guide_axis(cap = "both"), 
      y = guide_axis(cap = "both"))+
    theme(
      legend.position = "none",
      axis.line.x = element_line(),
      axis.title.y = element_blank(),
      axis.text.y = element_blank(),
      axis.ticks.y = element_blank(),
      axis.line.y = element_blank()
    ) +
    labs(y = "", x = "Най-добра комбинация")

   ggsave(
     "combinaion-top-bg.png",
     units = "mm",
     bg = "white",
     width = 300,
     height = 200,
     dpi = 1000
   )

  
  
worse_combination <-  
  bg |>
    mutate(rowid = row_number()) |>
    select(-c(2:4)) |>
    pivot_longer(cols = 15:34,
                 names_to = "var",
                 values_to = "value") |>
    separate(
      var,
      into = c("cluster", "alternative"),
      sep = "_",
      extra = "merge",
      fill = "right"
    ) |>  
  group_by(cluster,rowid) |>
  slice_min(value, n = 1) |>
  ungroup() |>
  count(cluster, alternative) |>
  group_by(cluster) |>
  mutate(sum = sum(n)) |>
  slice_min(n, n = 1) |>
  mutate(group = paste0(cluster, "_", alternative)) |>
  ungroup() |>
  select(group, n, sum) |>
  mutate(
      group = case_when(
        group == "def_conservative" ~ "Консервативна дефиниция",
        group == "funding_balanced" ~ "Балансирано финансиране",
        group == "newmed_balanced" ~ "Балансирани критерии за реимбурсация",
        group == "organisation_status_quo" ~ "Статукво на организацията",
        group == "reg_balanced" ~ "Балансиран модел на регистрация"
      )) |> 
    pcit() |>
    ggplot(aes(
      x = proportion,
      y = fct_reorder(group, proportion),
      fill = group
    )) +
    geom_col(width = .5, 
             alpha = 0.6,
             color = "gray10") +
    geom_text(
      aes(label = group, x = 0),
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
    breaks = c(seq(0, .6, 0.2)),
    labels = scales::label_percent()
  ) +
    scale_y_discrete(guide = "none") +
    scale_fill_manual(values = 
                        c("Консервативна дефиниция" = "#C7253E",
                          "Балансирано финансиране" = "#E85C0D",
                          "Балансирани критерии за реимбурсация" = "#41B3A2",
                          "Статукво на организацията" = "#0D7C66",
                          "Балансиран модел на регистрация" = "#013440")) +
    guides(
      x = guide_axis(cap = "both"), 
      y = guide_axis(cap = "both"))+
    theme(
      legend.position = "none",
      axis.line.x = element_line(),
      axis.title.y = element_blank(),
      axis.text.y = element_blank(),
      axis.ticks.y = element_blank(),
      axis.line.y = element_blank()
    ) +
    labs(y = "", x = "Най-слабо предпочитана комбинация")

  
combination_top + worse_combination

bg |>
  mutate(rowid = row_number()) |>
  select(-c(2:4)) |>
  pivot_longer(cols = 15:34,
               names_to = "var",
               values_to = "value") |>
  separate(
    var,
    into = c("cluster", "alternative"),
    sep = "_",
    extra = "merge",
    fill = "right"
  ) |>
  group_by(rowid, cluster) |>
  slice_max(value, n = 1) |>
  ungroup() |>
  count(institution_1,cluster, alternative) |>
  group_by(institution_1,cluster) |>
  mutate(sum = sum(n)) |>
  slice_max(n, n = 1) |>
  mutate(group = paste0(cluster, "_", alternative)) |>
  ungroup() |>
  select(institution_1,group, n, sum) |>
  pcit()

bg |> 
  select(18:37) |> 
  correlation(redundant = TRUE) |>
  tibble() |> 
  separate(
    Parameter1,
    into = c("cluster1", "alternative1"),
    sep = "_",
    extra = "merge",
    fill = "right"
  ) |>
  separate(
    Parameter2,
    into = c("cluster2", "alternative2"),
    sep = "_",
    extra = "merge",
    fill = "right"
  ) |>
  filter(cluster1 != cluster2) |>
  filter(cluster1 > cluster2) |>
  filter(p < 0.05)

library(tidyclust)
set.seed(838383)

clust_data <- 
  bg |> 
  select(-c(2:4)) |> 
  to_dummmy() 


hc_spec <- hier_clust(
  num_clusters = 2,
  linkage_method = "ward.D2"
)

hc_fit <- hc_spec %>%
  fit(~ .,
      data = clust_data
  )

hc_fit$fit %>% plot()

hc_fit$fit %>%as.dendrogram()


clusters <- 
  hc_fit |> 
  augment(new_data = clust_data) |> 
  rename(hc_clusters = .pred_cluster)

kmeans_spec <- k_means(num_clusters = 2)
kmeans_fit <- kmeans_spec |> 
  fit(~ .,
      data = clust_data
  )

clusters <- 
  kmeans_fit  |> 
  augment(clusters) |> 
  rename(kmeans_clusters = .pred_cluster) 
  
clusters |> 
  filter(hc_clusters != kmeans_clusters) 

kmeans_fit %>%
  silhouette_avg(clust_data)

hc_fit %>%
  silhouette_avg(clust_data)

set.seed(123)

# function to compute total within-cluster sum of square 
wss <- function(k) {
  kmeans(clust_data, k, nstart = 10 )$tot.withinss
}

# Compute and plot wss for k = 1 to k = 15
k.values <- 1:15

# extract wss for 2-15 clusters
wss_values <- map_dbl(k.values, wss)

plot(k.values, wss_values,
     type="b", pch = 19, frame = FALSE, 
     xlab="Number of clusters K",
     ylab="Total within-clusters sum of squares")


factoextra::fviz_nbclust(clust_data, 
                         kmeans, 
                         k.max = 15,
                         method = "silhouette")+
  theme_nice+
  guides(x = guide_axis(cap = "both"), y = guide_axis(cap = "both")) +
  theme(axis.line = element_line(),
        axis.text = element_text(family = "Sofia Sans Condensed", size = 20),
        axis.title = element_text(family = "Sofia Sans Condensed", size = 20),
        legend.position = "none")+
  labs(x = "# Клъстери", y = "Силует", 
       title = "")

ggsave(
  "silhouette-bg.png",
  units = "mm",
  bg = "white",
  width = 180,
  height = 120,
  dpi = 1000
)


clusters |> 
  mutate(across(c(1,4:11,34:40), as.factor)) |> 
  arsenal::tableby(kmeans_clusters ~ ., data= _) |> 
  summary(text = TRUE)

tb <- 
  clusters |> 
  mutate(across(c(1,4:11,34:40), as.factor)) |> 
  tableone::CreateTableOne(strata = "kmeans_clusters" , data = _)


clusters |> 
  select(kmeans_clusters, 14:33) |> 
  pivot_longer(2:21, names_to = "var", values_to = "value") |>
  mutate(
    fct = case_when(
      value == 1 ~ "Disagree",
      value == 2 ~ "Disagree",
      value == 3 ~ "Neutral",
      value == 4 ~ "Agree",
      value == 5 ~ "Agree"
    )) |>
  count(var,kmeans_clusters,fct) |>
  pivot_wider(names_from = fct, values_from = n) |>
  mutate(sum = Agree + Disagree + Neutral) |>
  mutate(agr = Agree + 0.5 * Neutral) |> 
  select(-c(Disagree, Neutral, Agree)) |>
  mutate(agr = as.integer(agr), 
         sum = as.integer(sum)) |>
  select(var, kmeans_clusters,agr, sum) |>
  pcit() |>
  compare_proportions_by() |>
  select(kmeans_clusters, var, proportion,lower,upper) |> 
  mutate(across(c(3:5), function(x) x*100)) |>
  mutate_round() 
  
  
  
  
  
  